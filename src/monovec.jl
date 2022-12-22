export monovec, monovectype, emptymonovec, sortmonovec, mergemonovec

"""
    abstract type AbstractMonomialOrdering end

Abstract type for monomial ordering as defined in [CLO15, Definition 2.2.1, p. 55]

[CLO13] Cox, D., Little, J., & OShea, D.
*Ideals, varieties, and algorithms: an introduction to computational algebraic geometry and commutative algebra*.
Springer Science & Business Media, **2013**.
"""
abstract type AbstractMonomialOrdering end

"""
    abstract type AbstractGradedMonomialOrdering end

Abstract type for monomial ordering for which `a < b` when `degree(a) < degree(b)`.

[CLO13] Cox, D., Little, J., & OShea, D.
*Ideals, varieties, and algorithms: an introduction to computational algebraic geometry and commutative algebra*.
Springer Science & Business Media, **2013**.
"""
abstract type AbstractGradedMonomialOrdering <: AbstractMonomialOrdering end

"""
    struct LexOrder <: AbstractMonomialOrdering end

Lexicographic (Lex for short) Order often abbreviated as *lex* order as defined in [CLO15, Definition 2.2.3, p. 56]

See [`GradedLexOrder`](@ref) for the graded version.

[CLO13] Cox, D., Little, J., & OShea, D.
*Ideals, varieties, and algorithms: an introduction to computational algebraic geometry and commutative algebra*.
Springer Science & Business Media, **2013**.
"""
struct LexOrder <: AbstractMonomialOrdering end

"""
    struct GradedLexOrder <: AbstractGradedMonomialOrdering end

Graded Lex Order often abbreviated *grlex* order as defined in [CLO15, Definition 2.2.3, p. 56]

See [`LexOrder`](@ref) for the non-graded version.

[CLO13] Cox, D., Little, J., & OShea, D.
*Ideals, varieties, and algorithms: an introduction to computational algebraic geometry and commutative algebra*.
Springer Science & Business Media, **2013**.
"""
struct GradedLexOrder <: AbstractGradedMonomialOrdering end

"""
    struct InverseLexOrder <: AbstractMonomialOrdering end

Inverse Lex Order defined in [CLO15, Exercise 2.2.6, p. 61] where it is abbreviated as *invlex*.
It corresponds to [`LexOrder`](@ref) but with the variables in reverse order.

See [`GradedInverseLexOrder`](@ref) for the graded version.

[CLO13] Cox, D., Little, J., & OShea, D.
*Ideals, varieties, and algorithms: an introduction to computational algebraic geometry and commutative algebra*.
Springer Science & Business Media, **2013**.
"""
struct InverseLexOrder <: AbstractMonomialOrdering end

"""
    struct GradedInverseLexOrder <: AbstractGradedMonomialOrdering end

Graded Inverse Lex Order that can be abbreviated as *grinvlex* order.
It is defined in [BDD13, Definition 2.1] where it is called *Graded xel order*.

See [`InverseLexOrdering`](@ref) for the non-graded version.

[BDD13] Batselier, K., Dreesen, P., & De Moor, B.
*The geometry of multivariate polynomial division and elimination*.
SIAM Journal on Matrix Analysis and Applications, 34(1), 102-125, *2013*.
"""
struct GradedInverseLexOrder <: AbstractGradedMonomialOrdering end

"""
    struct ReverseLexOrder <: AbstractMonomialOrdering end

Reverse Lex Order defined in [CLO15, Exercise 2.2.9, p. 61] where it is abbreviated as *rinvlex*.
It corresponds to the reverse of the [`InverseLexOrder`](@ref), that is,
`compare(a, b, ReverseLexOrder()) = -compare(a, b, InverseLexOrder)`.

See [`GradedReverseLexOrder`](@ref) for the graded version.

[CLO13] Cox, D., Little, J., & OShea, D.
*Ideals, varieties, and algorithms: an introduction to computational algebraic geometry and commutative algebra*.
Springer Science & Business Media, **2013**.
"""
struct ReverseLexOrder <: AbstractMonomialOrdering end

"""
    struct GradedReverseLexOrder <: AbstractGradedMonomialOrdering end

Graded Reverse Lex Order often abbreviated *grevlex* order as defined in [CLO15, Definition 2.2.6, p. 58]

See [`ReverseLexOrdering`](@ref) for the non-graded version.

[CLO13] Cox, D., Little, J., & OShea, D.
*Ideals, varieties, and algorithms: an introduction to computational algebraic geometry and commutative algebra*.
Springer Science & Business Media, **2013**.
"""
struct GradedReverseLexOrder <: AbstractGradedMonomialOrdering end

monomials(v::AbstractVariable, degree, args...) = monomials((v,), degree, args...)

"""
    emptymonovec(p::AbstractPolynomialLike)

Returns an empty collection of the type of `monomials(p)`.
"""
emptymonovec(p) = monomialtype(p)[]

"""
    monovec(X::AbstractVector{MT}) where {MT<:AbstractMonomialLike}

Returns the vector of monomials `X` in decreasing order and without any duplicates.

### Examples

Calling `monovec` on ``[xy, x, xy, x^2y, x]`` should return ``[x^2y, xy, x]``.
"""
function monovec(X::AbstractVector{MT}) where {MT<:AbstractMonomial}
    Y = sort(X)
    dups = findall(i -> Y[i] == Y[i-1], 2:length(Y))
    deleteat!(Y, dups)
    Y
end
monovec(X::AbstractVector{TT}) where {TT<:AbstractTermLike} = monovec(AbstractVector{monomialtype(TT)}(X))

"""
    monovec(a, X::AbstractVector{MT}) where {MT<:AbstractMonomialLike}

Returns `b, Y` where `Y` is the vector of monomials of `X` in decreasing order
and without any duplicates and `b` is the vector of corresponding coefficients
in `a`, where coefficients of duplicate entries are summed together.

### Examples

Calling `monovec` on ``[2, 1, 4, 3, -1], [xy, x, xy, x^2y, x]`` should return
``[3, 6, 0], [x^2y, xy, x]``.
"""
function monovec(a, x)
    if length(a) != length(x)
        throw(ArgumentError("There should be as many coefficient than monomials"))
    end
    σ, X = sortmonovec(x)
    b = a[σ]
    if length(x) > length(X)
        rev = Dict(X[j] => j for j in eachindex(σ))
        for i in eachindex(x)
            j = rev[x[i]]
            if i != σ[j]
                b[j] += a[i]
            end
        end
    end
    return b, X
end

"""
    monovectype(X::AbstractVector{MT}) where {MT<:AbstractMonomialLike}

Returns the return type of `monovec`.
"""
monovectype(X::Union{AbstractVector{PT}, Type{<:AbstractVector{PT}}}) where {PT<:APL} = monovectype(PT)
monovectype(::Union{PT, Type{PT}}) where {PT <: APL} = Vector{monomialtype(PT)}

# If there are duplicates in X, the coefficients should be summed for a polynomial and they should be equal for a measure.
"""
    sortmonovec(X::AbstractVector{MT}) where {MT<:AbstractMonomialLike}

Returns `σ`, the orders in which one must take the monomials in `X` to make them sorted and without any duplicate and the sorted vector of monomials, i.e. it returns `(σ, X[σ])`.

### Examples

Calling `sortmonovec` on ``[xy, x, xy, x^2y, x]`` should return ``([4, 1, 2], [x^2y, xy, x])``.
"""
function sortmonovec(X::AbstractVector{MT}) where {MT<:AbstractMonomial}
    σ = sortperm(X)
    dups = findall(i -> X[σ[i]] == X[σ[i-1]], 2:length(σ))
    deleteat!(σ, dups)
    σ, X[σ]
end
sortmonovec(X::AbstractVector{TT}) where {TT<:AbstractTermLike} = sortmonovec(AbstractVector{monomialtype(TT)}(X))
sortmonovec(X::Tuple) = sortmonovec(vec(X))

"""
    mergemonovec{MT<:AbstractMonomialLike, MVT<:AbstractVector{MT}}(X::AbstractVector{MVT}}

Returns the vector of monomials in the entries of `X` in decreasing order and without any duplicates, i.e. `monovec(vcat(X...))`

### Examples

Calling `mergemonovec` on ``[[xy, x, xy], [x^2y, x]]`` should return ``[x^2y, xy, x]``.
"""
mergemonovec(X) = monovec(vcat(X...))
