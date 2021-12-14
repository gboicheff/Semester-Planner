using Catlab
using Catlab.CategoricalAlgebra
using Catlab.Graphs
using Catlab.Graphs.BasicGraphs
using Catlab.Graphics
using Catlab.Graphics.Graphviz
using Catlab.Graphics.GraphvizGraphs
using Catlab.Graphs.PropertyGraphs
using Catlab.CategoricalAlgebra.CSets
using Catlab.CategoricalAlgebra.FinSets, Catlab.CategoricalAlgebra
using DataStructures
using Colors
using Random


struct Preorder
    carrier:: FinSet
    relation :: SortedSet{Pair{Int,Int}}
    """Construct valid preorder by taking reflexive/transitive closure"""
    function Preorder(carrier:: FinSet, rel :: Vector{Pair{Int,Int}})
      for (a,b) ∈ rel
        a ∈ carrier && b ∈ carrier || error("relation element not in carrier set")
      end
      relation = SortedSet(rel)
      for (a, b, c) in Iterators.product(carrier, carrier, carrier)
        if ((a => b) ∈ relation) && ((b => c) ∈ relation)
          push!(relation, a => c) # enforces relation is transitive
        end
      end
      for i in carrier
        push!(relation, i => i) # enforces that relation is reflexive
      end
      return new(carrier, relation)
    end
  end

# function to parse major requirement files
function load_major(path::String, taken_classes::Set{String}=Set{String}())

    file = open(path, "r")

    num_to_class = Dict()
    class_to_num = Dict()

    relations = Vector{Pair{Int, Int}}()

    num_classes = 0
    while !eof(file)
        line = readline(file)
        if length(strip(line, ' ')) != 0
            sp = split(line, ":")

            if length(sp) >= 1
                name = strip(sp[1], ' ')
                if !in(name, taken_classes)
                    num_classes+=1
                    num_to_class[num_classes] = string(name)
                    class_to_num[string(name)] = num_classes
                end

                if length(sp) >= 2
                    reqs_str = strip(sp[2], ['[', ']', ' '])
                    reqs = split(reqs_str, ",")
                    
                    for req in reqs
                        req = strip(req, ' ')
                        if length(req) > 0
                            if !in(req, taken_classes) && in(name, taken_classes)
                                throw("At least one class taken has missing prereqs!")
                            end
                            if !in(req, taken_classes)
                                push!(relations, class_to_num[req] => class_to_num[name])
                            end
                        end
                    end
                end
            end
        end
    end

    close(file)


    return (Preorder(FinSet(num_classes),relations), num_to_class)
end

# finds elements with no edges in or out
function find_one_offs(preorder::Preorder)
    one_offs = Vector()
    d = Dict()
    for class in collect(preorder.carrier)
        d[class] = true
    end
    for (a,b) in preorder.relation
        if a != b
            d[a] = false
            d[b] = false
        end
    end
    for (class, is_one_off) in d
        if is_one_off
            push!(one_offs, class)
        end
    end
    return Set(one_offs)
end

function generate_schedule(preorder::Preorder, num_semesters::Int=8, seed::Int=0)
    Random.seed!(seed)

    classes = collect(preorder.carrier)
    reqs = preorder.relation

    full_schedule = Vector()

    one_off_classes = find_one_offs(preorder)


    # build dictionary of in counts like in topological sort
    in_counts = Dict()
    for class in classes
        # ignore one off classes for now
        if !(class in one_off_classes)
            in_counts[class] = 0
            for (a,b) in preorder.relation
                if class == b && a != b
                    in_counts[class]+=1
                end
            end
        end
    end


    # schedule classes with prereqs
    for index in 1:num_semesters
        semester_schedule = Vector()

        available_classes = Set(collect(in_counts))

        # find bottoms
        # marking them for deletion
        for (class, in_count) in shuffle!(collect(available_classes))
            if in_count == 0 && length(semester_schedule) < ceil(length(preorder.carrier)/num_semesters)
                push!(semester_schedule, class)
            end
        end

        # delete taken classes
        for class in semester_schedule
            for (a,b) in preorder.relation
                if class == a
                    in_counts[b]-=1
                end
            end
            delete!(in_counts, class)
        end

        push!(full_schedule, semester_schedule)
    end


    # schedule classes with no prereqs
    # prioritizing even credit distribution
    while length(one_off_classes) > 0
        
        # find semester with min number of credits
        min_index = 1
        for (index, semester) in enumerate(full_schedule)
            if length(full_schedule[index]) < length(full_schedule[min_index])
                min_index = index
            end 
        end
        
        class_to_add = collect(one_off_classes)[1]
        push!(full_schedule[min_index], class_to_add)
        delete!(one_off_classes, class_to_add)
    end

    # check that all classes were fit into the schedule
    if length(one_off_classes) > 0 || length(collect(in_counts)) > 0
        throw("Cannot generate schedule!")
    end

    return full_schedule
end

function convert_to_readable(schedule, mapping)
    for (i,semester_schedule) in enumerate(schedule)
        for (j,semester_schedule) in enumerate(semester_schedule)
            schedule[i][j] = mapping[schedule[i][j]]
        end
    end
    return schedule
end

function output_plan(schedule, file_path::String, mapping)
    file = open(file_path, "w")
    for semester_schedule in schedule
        for (index, class) in enumerate(semester_schedule)
            if index == length(semester_schedule)
                print(file, mapping[class])
            else
                print(file, mapping[class] * ", ")
            end
        end
        println(file, "")
    end
    close(file)
end

struct Monotone_map
    domain::Preorder
    codomain::Preorder
    mapping::FinFunction
    function Monotone_map(domain::Preorder, cod::Preorder, mapping::FinFunction)
      ((dom(mapping) == domain.carrier) && (codom(mapping) == cod.carrier)
      ) || error("mapping mismatch")
      return new(domain,cod,mapping)
    end
  end


function is_monotone(mm::Monotone_map)::Bool
    for comp in mm.domain.relation
        mapL = mm.mapping(comp.first)
        mapR = mm.mapping(comp.second)
        mono=false
        
        if(comp.first == comp.second) #reflexive relation
          continue
        end
        if(mapL == mapR) #pre req and class taken in same semeester
          return false;
        end

        for comparison in mm.codomain.relation

            if(mapL == comparison.first && mapR == comparison.second)
                mono=true
            end
        end
        if(!mono)
            return false
        end
    end
    return true
end

function load_taken_classes(path::String)::Set{String}
    lines = readlines(path)
    classes = Set{String}()
    for line in lines
        l_classes = split(line, ", ")
        for class in l_classes

            push!(classes, class)
        end
    end
    return classes
end

function main()


    if length(ARGS) < 3
        throw("Missing args")
    end

    major_paths = Dict(["CS"=>"reqs/CS.reqs"])

    major = ARGS[1]
    classes_taken_path = ARGS[2]
    num_semesters = parse(Int,ARGS[3])

    if !haskey(major_paths, major)
        throw("Invalid major")
    end

    semester_preorder = Preorder(FinSet(num_semesters), [x=>x+1 for x in 1:num_semesters-1])

    classes_taken = load_taken_classes(classes_taken_path)

    major, major_mapping = load_major(major_paths[major], classes_taken)
    schedule = generate_schedule(major, num_semesters)


    indices = Vector{Int}(undef,length(major.carrier))

    for (index,semester) in enumerate(schedule)
        for class in semester
            indices[class] = index
        end
    end

    f = FinFunction(indices, major.carrier, semester_preorder.carrier)
    schedule_map = Monotone_map(major, semester_preorder, f)

    if !is_monotone(schedule_map)
        throw("Couldn't generate valid monotone map!")
    end

    readable_schedule = convert_to_readable(schedule, major_mapping)

    for (index,semester) in enumerate(readable_schedule)
        print("Semester ")
        print(index)
        print(": ")
        for (inner_index,class) in enumerate(semester)
            if inner_index == length(semester)
                print(class)
            else
                print(class * ", ")
            end
        end
        println()
    end

end

main()
