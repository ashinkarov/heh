function heh_tup2arr(t::Tuple)
    return [t...]
end

function heh_arr2tup(a::Array)
    return (a...)
end

function heh_access_array(a::Array, t::Array)
    return getindex(a, t...)
end

function heh_create_array(args...)
    ArraysOrInts = Union{Array, Int}

    if length(args) == 0
        res = []
    else
        if isa(args[1], Number)
            res = [x for x in args]
        elseif isa(args[1], Array)
            # create a n-dim array from
            # array of array
            # FIXME, lies, this is not n-dim!
            tmp = [args...]
            res = vcat(tmp...)
        else
            throw(TypeError(:heh_create_array, "Incorrect type given", ArraysOrInts, args[1]))
        end
    end

    return res
end

function heh_imap(s1::Array, s2::Array, f)
    vals = similar(Array{Array}, heh_arr2tup(s1))

    # populate vals with all 'indices'
    for idx in eachindex(vals)
        vals[idx] = heh_tup2arr(ind2sub(vals, idx))
    end
    return map(f, vals)
end

function heh_reduce(f, neut, a)
    res = neut
    for x in eachindex(a)
        res = f(x, res)
    end

    return res
end

function heh_filter(p, a::Array)
    return filter(p, a)
end

function heh_shape(a::Array)
    return heh_tup2arr(size(a))
end

function heh_islim(a)
    return false
end

function heh_inrange(iv::Array, lb::Array, ub::Array)
    return all(lb .< iv) && all(iv .<= ub)
end
