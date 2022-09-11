# Trebor: an implementation of Observational Type Theory (OTT) and more

This project is created to encourage the internal cat of a particular donut
to implement some full-scale type checker/dependently typed language.

![](pohai/trebor-dont-want-to-impl-typechecker.png)
![](pohai/trebor-dont-want-to-impl-typechecker2.png)
![](pohai/trebor-dont-want-to-impl-typechecker3.png)

## Feature Overview

- [Observational Equality](#Observational-Equality)
- (WIP) [Universe Polymorphism a là Conor McBride](#Universe-Polymorphism)


## Observational Equality

![](pohai/trebor-on-set-theory.png)

Extensional equality principles are very useful for
both math formalization and proving program properties,
but has long been a second-class citizen in proof assistants due to technical difficulties.
OTT [[1]](#ref-1) [[2]](#ref-2) [[3]](#ref-3) is an approach to integrate
extensional principles into intensional type theory,
while retaining good metatheory properties like canonicity and strong normalization.

AFAIK, OTT is currently the most promising approach to extensional equality principles:

| type theory | funext | UIP | canonicity | normalization   | regularity<sup>1</sup> |
|-------------|--------|-----|------------|-----------------|------------------------|
| ITT         | no     | no  | yes        | yes             | yes                    |
| ITT + axiom | yes    | yes | no         | yes             | yes                    |
| ITT + irr.  | no     | yes | yes        | yes<sup>2</sup> | yes                    |
| ETT         | yes    | yes | yes        | no<sup>3</sup>  | yes                    |
| HoTT        | yes    | no  | no         | yes             | yes                    |
| Cubical TT  | yes    | no  | yes        | yes (no NBE yet)| no/difficult           |
| OTT         | yes    | yes | yes        | yes             | possible (see [[2]](#ref-2))|

1: whether eliminating `refl` computes to the identity.

2: there are sound NBE implementations that lack universe hierarchy [[4]](#ref-4).
However, adding too much irrelevance and impredicativity breaks normalization [[5]](#ref-5)

3: type checking ETT itself is very difficult, due to the need to automatically "guess"
propositional equalities.
This difficulty can be avoided by requiring user annotations [[6]](#ref-6).
But even so, ETT fails to normalize (e.g. see [[6]](#ref-6)) in the presence of universe/large elimination.
Also, ETT allows ill-typed open terms such as `0 1` or `fst (\x. x)`,
making type-directed normalization very difficult. See [[7]](#ref-7) for some discussions.



Despite its good properties, there seems to be many different ways to implement/formalize OTT.
[[1]](#ref-1) [[2]](#ref-2) [[3]](#ref-3) and an existing implementation [[8]](#ref-8) all use different approaches:

- In [[1]](#ref-1), observational equalities are built using builtin constructors.
This requires a set of primitive constructors for every type former.

- In [[2]](#ref-2), the equality type *computes* to the type of its proof/witness.
But I am afraid that this will make type checking difficult:
the endpoints of an equality type is hard to retrieve after it computes to something else.

The type system in [[2]](#ref-2) uses a separate (definitionally) proof-irrelevant
proposition fragment to support (definitional) UIP.

[[2]](#ref-2) also stresses the issue of regularity.
Without regularity, elimination of inductive types may have undesirable computational behavior.
The authors propose adding a regularity rule to overcome this problem,
implementation may be similar to [[4]](#ref-4)


- [[3]](#ref-3) also adapts the "equality type computes to proof" approach
and definitional irrelevance in [[2]](#ref-2).
However, while both [[1]](#ref-1) and [[2]](#ref-2) uses an heterogenous equality,
[[3]](#ref-3) features homogeneous equality.
It also supports *propositional* regularity.
But I am worried that this may cause some kind of coercion hell.

- [[8]](#ref-8) is the only implementation I found for OTT online.
It features quotient type, normalization-by-evaluation and regularity.
The NBE algorithm erases all equality proofs,
which is good computationally,
but probably not so desirable from a formalization point of view.


In this project, my approach to implement OTT is:

- equality types are heterogeneous, don't compute to something else,
and are definitionally proof irrelevant
- *no* primitive equality constructors,
all necessary operations on equalities are supported via *axioms*
- so long as all axioms are irrelevant, canonicity would be safe
- support definitional regularity, following the approach in [[4]](#ref-4)
- equality proofs are not erased,
but perhaps wrapped in lazy thunks to avoid unnecessary computation

## Universe Polymorphism

![](pohai/trebor-on-univ-poly.png)

Universe hierarchy and polymorphism here
follows the proposal of Conor McBride [[9]](#ref-9) [[10]](#ref-10).
In this style of universe hierarchy:

- viewing a small type from a larger universe is done implicitly
via bidirectional type checking and subtyping

- the universe level of a global definition is the smallest possible value ("build on the ground"),
no level variables needed

- *enlarging* a small type (i.e. "shift to higher", universe polymorphism)
is done via a explicit operator `~`.
The operator accumulates on global variables and is structural on all other term formers



## License
This project is distributed under the zero clause BSD license. See `LICENSE`.


## References

<a id="ref-1" href="https://personal.cis.strath.ac.uk/conor.mcbride/ott.pdf">[1]</a>
Towards Observational Equality

<a id="ref-2" href="http://www.cs.nott.ac.uk/~psztxa/publ/obseqnow.pdf">[2]</a>
Observational Equality, Now!

<a id="ref-3" href="https://hal.inria.fr/hal-03367052/document">[3]</a>
Observational Equality: Now For Good!

<a id="ref-4" href="https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.158.2321&rep=rep1&type=pdf">[4]</a>
Extensional Normalization in the Logical Framework with Proof Irrelevant Equality

<a id="ref-5" href="https://arxiv.org/pdf/1911.08174.pdf">[5]</a>
Failure of Normalization in Impredicative Type Theory with Proof-irrelevant Propositional Equality

<a id="ref-6" href="http://homepage.divms.uiowa.edu/~astump/papers/ITRS10-long.pdf">[6]</a>
Equality, Quasi-Implicit Products, and Large Eliminations

<a id="ref-7" href="https://proofassistants.stackexchange.com/questions/1301/tutorial-implementations-of-extensional-type-theories">[7]</a>
<https://proofassistants.stackexchange.com/questions/1301/tutorial-implementations-of-extensional-type-theories>

<a id="ref-8" href="https://github.com/bobatkey/sott">[8]</a>
<https://github.com/bobatkey/sott>

<a id="ref-9" href="https://personal.cis.strath.ac.uk/conor.mcbride/Crude.pdf">[9]</a>
<https://personal.cis.strath.ac.uk/conor.mcbride/Crude.pdf>

<a id="ref-10" href="https://pigworker.wordpress.com/2015/01/09/universe-hierarchies/">[10]</a>
<https://pigworker.wordpress.com/2015/01/09/universe-hierarchies/>
