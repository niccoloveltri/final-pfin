# Type Theoretic Constructions of the Final Coalgebra of the Finite Powerset Functor
## Niccolò Veltri

The finite powerset functor is a construct frequently employed for the specification of nondeterministic
transition systems as coalgebras. The final coalgebra of the finite powerset functor, whose elements
characterize the dynamical behavior of transition systems, is a well-understood object which enjoys
many equivalent presentations in set theoretic foundations based on classical logic.

In this paper, we discuss various constructions of the final coalgebra of the finite powerset functor
in constructive type theory, and we formalize our results in the Cubical Agda proof assistant. Using
setoids, the final coalgebra of the finite powerset functor can be defined from the final coalgebra of
the list functor. Using types instead of setoids, as it is common in homotopy type theory, one can
specify the finite powerset datatype as a higher inductive type and define its final coalgebra as a
coinductive type. Another construction is obtained by quotienting the final coalgebra of the list
functor, but the proof of finality requires the assumption of the axiom of choice. We conclude the
paper with an analysis of a classical construction by James Worrell, and show that its adaptation to
our constructive setting requires the presence of classical axioms such as countable choice and the
lesser limited principle of omniscience.
