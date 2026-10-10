import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

namespace Note198.FiniteTailCoproduct
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (f : ℕ → C) (t : ℕ) [HasBiproduct (fun i : Fin t => f i)]

/-- The original count inclusions, with zero maps on the extinct tail. -/
def cofan : Cofan f := Cofan.mk (⨁ fun i : Fin t => f i)
  (fun n => if h : n < t then biproduct.ι (fun i : Fin t => f i) ⟨n,h⟩ else 0)

/-- A finite surviving prefix computes the actual infinite coproduct whenever
all objects in its tail are zero. This also includes the empty prefix. -/
def isColimit (hz : ∀ n, t ≤ n → IsZero (f n)) : IsColimit (cofan f t) where
  desc s := biproduct.desc (fun i : Fin t => s.ι.app ⟨i.val⟩)
  fac s n := by
    rcases n with ⟨n⟩
    by_cases h : n < t
    · simp [cofan,h]
    · simpa [cofan,h] using (hz n (Nat.le_of_not_gt h)).eq_of_src
        (0 : f n ⟶ s.pt) (s.ι.app ⟨n⟩)
  uniq s m hm := by
    apply biproduct.hom_ext'
    intro i
    simpa [cofan,i.isLt] using hm ⟨i.val⟩

/-- The comparison is an isomorphism in the ambient category, rather than
only equality of cohomology or a finite numerical count. -/
def iso [HasColimit (Discrete.functor f)]
    (hz : ∀ n, t ≤ n → IsZero (f n)) :
    (⨁ fun i : Fin t => f i) ≅ colimit (Discrete.functor f) :=
  (isColimit f t hz).coconePointUniqueUpToIso (colimit.isColimit _)

theorem finite_prefix_computes_coproduct [HasColimit (Discrete.functor f)]
    (hz : ∀ n, t ≤ n → IsZero (f n)) :
    Nonempty ((⨁ fun i : Fin t => f i) ≅ colimit (Discrete.functor f)) :=
  ⟨iso f t hz⟩

end
end Note198.FiniteTailCoproduct
