{-# OPTIONS --cubical --no-import-sorts #-}

-- =================================================================
-- Type Theoretic Constructions of the Final Coalgebra of the Finite
-- Powerset Functor
--
-- Niccolò Veltri
-- =================================================================

module Everything where

-- some preliminaries
import Basics

-- basic list stuff
import ListStuff

-- setoids
import SetoidStuff

-- alternative formulation of axiom of choice
import AxiomChoice

-- relation liftings on lists
import ListRelations

-- non-wellfounded trees with ordered finite branching
import Trees

-- =================================================================

-- finite powerset using HITs

-- -- as a set quotient of lists
import Pfin.AsSetQuot

-- -- as the free join semilattice on a type
import Pfin.AsFreeJoinSemilattice

-- finite powerset preserves countable intersection (assuming
-- countable choice)
import Pfin.PreservesCountableIntersections

-- =================================================================

-- final coalgebra of finite powerset functor in setoids
import FinalCoalg.InSetoid

-- final coalgebra of finite powerset functor in types

-- -- as a set quotient of trees (assuming axiom of choice)
import FinalCoalg.InTypesAsSetQuot

-- -- as a coinductive type
import FinalCoalg.InTypesAsCoindType

-- =================================================================


-- analysis of Worrell's construction

-- -- ω-limits
import Worrell.Limits

-- -- the canonical algebra map of Vω is not surjective (here we use
-- -- PfinQ instead of Pfin, but we know that the two are equivalent,
-- -- see Pfin.AsSetQuot)
import Worrell.NoSurjAlgebra

-- -- assuming the canonical algebra map of Vω is injective implies
-- -- LLPO
import Worrell.FromInjectivity

-- -- LLPO and countable choice imply the injectivity of the canonical
-- -- algebra map of Vω
import Worrell.ToInjectivity

-- -- assuming the canonical projection from Vω2 to Vω is injective
-- -- implies LLPO, showing that Worrell's construction of the final
-- -- coalgebra of Pfin as a subset of Vω cannot be done fully
-- -- constructively
import Worrell.FromInjectivityOmega

-- -- assuming countable choice and injectivity of the canonical
-- -- algebra map of Vω (or, equivalently, LLPO), we have that Vω2 is
-- -- the final coalgebra of Pfin
import Worrell.Finality

