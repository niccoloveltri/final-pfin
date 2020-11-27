{-# OPTIONS --cubical --no-import-sorts #-}

-- ================================================================
-- Final Coalgebra of the Finite Powerset Functor in Agda
-- ================================================================

module Everything where

-- some preliminaries
import Preliminaries

-- relation liftings on lists
import ListRelations

-- non-wellfound finite-branchin trees
import Trees


-- finite powerset using HITs:

-- -- as the free join semilattice on a type
import Pfin.AsFreeJoinSemilattice

-- -- as a set quotient of lists
import Pfin.AsSetQuot



-- final coalgebra of finite powerset functor in setoids:

-- -- using the conductive type of trees
import FinalCoalgPfin.Setoid.AsCoindType

-- -- as an (ω+ω)-limit
-- -- (work in progress, so far I have showed that the final coalgebra
-- -- of the finite powerset functor is not an ω-limit)
import FinalCoalgPfin.Setoid.AsLimit



-- final coalgebra of finite powerset functor in types (sets):

-- -- as a set quotient of the type of trees (using axiom of choice)
import FinalCoalgPfin.Set.AsSetQuot

-- -- as a coinductive type 
import FinalCoalgPfin.Set.AsCoindType
