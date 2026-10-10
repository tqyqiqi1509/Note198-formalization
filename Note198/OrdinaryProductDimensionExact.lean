import Note198.ProductProjectiveDimension
import Note198.TensorGlobalDimensionHeight
import Note198.SelectingOrdinaryAlgebra
import OAI.Algebra.Finitistic.Ordinary.OrdinaryProductOpposite

namespace Note198
noncomputable section
open CategoryTheory OAI.LittleFinitistic OrdinarySimulation
open scoped TensorProduct
universe u v
section ProductBound
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (DB : DirectedBound.DirectedSystem k B 3) (l : ℕ)

include DB in
/-- The precise bound for the manuscript's actual product algebra, for every
module, with no finite-generation restriction. -/
theorem ordinary_product_module_dimension_le (M : ModuleCat.{max u v} (AlgebraD k l B)) :
    projectiveDimension M ≤ (l+2 : ℕ) := by
  have hB := DirectedBound.DirectedSystem.both_sides_projectiveDimension_le.{u,v} DB
  have hL (N : ModuleCat.{max u v} B) : projectiveDimension N ≤ (l+2 : ℕ) := by
    apply (hB.1 N).trans
    exact_mod_cast (show 3-1 ≤ l+2 by omega)
  exact ProductModules.product_module_bound B (B ⊗[k] ChainAlgebra k l) (l+2)
    hL (tensor_chain_module_projectiveDimension_le DB l) M

include DB in
theorem ordinary_product_opposite_module_dimension_le
    (M : ModuleCat.{max u v} (AlgebraD k l B)ᵐᵒᵖ) :
    projectiveDimension M ≤ (l+2 : ℕ) := by
  have hB := DirectedBound.DirectedSystem.both_sides_projectiveDimension_le.{u,v} DB
  have hL (N : ModuleCat.{max u v} Bᵐᵒᵖ) : projectiveDimension N ≤ (l+2 : ℕ) := by
    apply (hB.2 N).trans
    exact_mod_cast (show 3-1 ≤ l+2 by omega)
  exact ProductModules.opposite_product_module_bound B (B ⊗[k] ChainAlgebra k l) (l+2)
    hL (tensor_chain_opposite_module_projectiveDimension_le DB l) M

include DB in
theorem ordinary_product_global_dimension_le :
    (⨆ M : ModuleCat.{max u v} (AlgebraD k l B),projectiveDimension M) ≤ (l+2 : ℕ) ∧
    (⨆ M : ModuleCat.{max u v} (AlgebraD k l B)ᵐᵒᵖ,projectiveDimension M) ≤ (l+2 : ℕ) :=
  ⟨iSup_le (ordinary_product_module_dimension_le DB l),
    iSup_le (ordinary_product_opposite_module_dimension_le DB l)⟩
end ProductBound

namespace SelectingOrdinaryDimension
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)

theorem module_dimension_le (M : ModuleCat.{max u v} (SelectingOrdinaryAlgebra.D E S)) :
    projectiveDimension M ≤ (SelectingOrdinaryAlgebra.length E S+2 : ℕ) :=
  ordinary_product_module_dimension_le
    (ThreeVertexAlgebra.directedSystem (QuadraticEncoding.composition E.relations)) _ M

/-- In particular every term of every actual signed D-complex has the same
uniform ordinary module bound. The complex's degree does not enter this bound. -/
theorem complex_term_dimension_le
    (C : CochainComplex (ModuleCat.{max u v} (SelectingOrdinaryAlgebra.D E S)) ℤ) (i : ℤ) :
    projectiveDimension (C.X i) ≤ (SelectingOrdinaryAlgebra.length E S+2 : ℕ) :=
  module_dimension_le E S (C.X i)

theorem first_inflation_dimension_eq (M : ModuleCat.{max u v} (QuadraticEncoding.B E.relations)) :
    projectiveDimension ((ProductModules.firstInflation (QuadraticEncoding.B E.relations)
      ((QuadraticEncoding.B E.relations) ⊗[k] ChainAlgebra k
        (SelectingOrdinaryAlgebra.length E S))).obj M) = projectiveDimension M :=
  ProductProjectiveDimension.firstInflation_dimension_eq _ _ M

theorem second_inflation_dimension_eq (M : ModuleCat.{max u v}
    ((QuadraticEncoding.B E.relations) ⊗[k] ChainAlgebra k (SelectingOrdinaryAlgebra.length E S))) :
    projectiveDimension ((ProductModules.secondInflation (QuadraticEncoding.B E.relations)
      ((QuadraticEncoding.B E.relations) ⊗[k] ChainAlgebra k
        (SelectingOrdinaryAlgebra.length E S))).obj M) = projectiveDimension M :=
  ProductProjectiveDimension.secondInflation_dimension_eq _ _ M
end SelectingOrdinaryDimension
end
end Note198
