import OAI.Algebra.Finitistic.Ordinary.OrdinaryProductSecondDimension

/-! Exact projective dimensions of the actual central-idempotent product modules.
The value `⊥` for zero modules is retained throughout. -/
namespace Note198.ProductProjectiveDimension
noncomputable section
open CategoryTheory OAI.LittleFinitistic.ProductModules
universe u v
variable (L R : Type u) [Ring L] [Ring R]

def componentProjection (M : ModuleCat.{v} (L × R)) :
    M ⟶ (firstInflation L R).obj (firstObject L R M) := by
  letI : Module (L × R) (firstObject L R M) :=
    Module.compHom (firstObject L R M) (RingHom.fst L R)
  exact ModuleCat.ofHom (show M →ₗ[L × R]
    (firstInflation L R).obj (firstObject L R M) from
    { toFun := fun x => ⟨((1,0) : L × R) • x, by
        change ((1,0) : L × R) • (((1,0) : L × R) • x) = ((1,0) : L × R) • x
        rw [← mul_smul]
        have he : ((1,0) : L × R) * (1,0) = (1,0) := by ext <;> simp
        rw [he]⟩
      map_add' := fun x y => Subtype.ext (smul_add _ _ _)
      map_smul' := by
        intro d x
        apply Subtype.ext
        change ((1,0) : L × R) • (d • x) =
          ((d.1,0) : L × R) • (((1,0) : L × R) • x)
        rw [← mul_smul,← mul_smul]
        congr 1
        ext <;> simp })

lemma componentProjection_apply (M : ModuleCat.{v} (L × R)) (x : M) :
    ((componentProjection L R M).hom x).val = ((1,0) : L × R) • x := rfl

def inflatedComponentEquiv (M : ModuleCat.{v} L) :
    firstObject L R ((firstInflation L R).obj M) ≃ₗ[L] M where
  toFun x := x.val
  invFun x := ⟨x, by change (1 : L) • x = x; exact one_smul _ _⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem component_projective (P : ModuleCat.{v} (L × R)) [Projective P] :
    Projective (firstObject L R P) := by
  refine ⟨fun g E he => ?_⟩
  let g' := componentProjection L R P ≫ (firstInflation L R).map g
  let e := (firstInflation L R).map E
  letI : Epi e := (ModuleCat.epi_iff_surjective e).mpr
    ((ModuleCat.epi_iff_surjective E).mp he)
  let h := Projective.factorThru g' e
  let h' : firstObject L R P ⟶ _ := ModuleCat.ofHom
    { toFun := fun x => h.hom x.val
      map_add' := fun x y => h.hom.map_add x.val y.val
      map_smul' := fun r x => h.hom.map_smul ((r,0) : L × R) x.val }
  refine ⟨h', ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hh := congrArg (fun f => f.hom x.val) (Projective.factorThru_comp g' e)
  change E.hom (h.hom x.val) = g.hom x
  have hproj : (componentProjection L R P).hom x.val = x := by
    apply Subtype.ext
    rw [componentProjection_apply]
    exact x.property
  change E.hom (h.hom x.val) = g.hom ((componentProjection L R P).hom x.val) at hh
  rwa [hproj] at hh

instance component_additive : (firstFunctor.{u,v} L R).Additive where
  map_add := by intros; rfl

theorem component_preservesHomology :
    (firstFunctor.{u,v} L R).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro K hK
  rw [ShortComplex.moduleCat_exact_iff] at hK ⊢
  intro x hx
  have hx' : K.g.hom x.val = 0 := congrArg Subtype.val hx
  obtain ⟨y, hy⟩ := hK x.val hx'
  let y' := ((componentProjection L R K.X₁).hom y)
  refine ⟨y', ?_⟩
  have he : firstMap L R K.f y' = x := by
    apply Subtype.ext
    change K.f.hom ((componentProjection L R K.X₁).hom y).val = x.val
    rw [componentProjection_apply,K.f.hom.map_smul,hy,x.property]
  exact he

variable [Small.{v} L] [Small.{v} R]

theorem component_dimensionLE (n : ℕ) (M : ModuleCat.{v} (L × R))
    [HasProjectiveDimensionLE M n] :
    HasProjectiveDimensionLE (firstObject L R M) n := by
  induction n generalizing M with
  | zero =>
    have : Projective M := (projective_iff_hasProjectiveDimensionLE_zero (X := M)).mpr inferInstance
    have := component_projective L R M
    infer_instance
  | succ n ih =>
    let S := M.projectiveShortComplex
    have hS := M.shortExact_projectiveShortComplex
    have : HasProjectiveDimensionLT S.X₁ (n+1) :=
      (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp inferInstance
    have hk := ih S.X₁
    have hp := component_projective L R S.X₂
    have := component_preservesHomology.{u,v} L R
    have : Mono ((firstFunctor L R).map S.f) :=
      (ModuleCat.mono_iff_injective _).mpr (by
        intro x y h
        have hh : S.f.hom x.val = S.f.hom y.val :=
          congrArg (fun z : firstObject L R S.X₂ => z.val) h
        exact Subtype.ext (((ModuleCat.mono_iff_injective S.f).mp hS.mono_f) hh))
    have : Epi ((firstFunctor L R).map S.g) :=
      (ModuleCat.epi_iff_surjective _).mpr
        (firstMap_surjective L R S.g ((ModuleCat.epi_iff_surjective S.g).mp hS.epi_g))
    have hs : (S.map (firstFunctor L R)).ShortExact := hS.map (firstFunctor L R)
    exact (hs.hasProjectiveDimensionLT_X₃_iff n hp).mpr hk

/-- Bound preservation and preservation of the zero object imply the full extended
projective-dimension inequality, including infinite dimensions. -/
theorem dimension_le_of_bounds {A B : Type u} [Ring A] [Ring B]
    (M : ModuleCat.{v} A) (N : ModuleCat.{v} B)
    (hz : Limits.IsZero M → Limits.IsZero N)
    (hb : ∀ n : ℕ, HasProjectiveDimensionLE M n → HasProjectiveDimensionLE N n) :
    projectiveDimension N ≤ projectiveDimension M := by
  refine le_of_forall_ge (fun d hd => ?_)
  induction d with
  | bot =>
    apply le_of_eq
    apply (projectiveDimension_eq_bot_iff N).mpr
    exact hz ((projectiveDimension_eq_bot_iff M).mp (le_bot_iff.mp hd))
  | coe d =>
    induction d with
    | top => exact le_top
    | coe n =>
      exact (projectiveDimension_le_iff N n).mpr
        (hb n ((projectiveDimension_le_iff M n).mp hd))

theorem component_dimension_le (M : ModuleCat.{v} (L × R)) :
    projectiveDimension (firstObject L R M) ≤ projectiveDimension M := by
  apply dimension_le_of_bounds M (firstObject L R M)
  · intro hz
    rw [ModuleCat.isZero_iff_subsingleton] at hz ⊢
    letI := hz
    infer_instance
  · intro n hn
    letI := hn
    exact component_dimensionLE L R n M

theorem firstInflation_dimension_eq (M : ModuleCat.{v} L) :
    projectiveDimension ((firstInflation L R).obj M) = projectiveDimension M := by
  apply le_antisymm
  · apply dimension_le_of_bounds M ((firstInflation L R).obj M)
    · intro hz
      rw [ModuleCat.isZero_iff_subsingleton] at hz ⊢
      exact hz
    · intro n hn
      letI := hn
      exact firstInflation_dimensionLE L R n M
  · rw [← ModuleCat.projectiveDimension_eq_of_linearEquiv (inflatedComponentEquiv L R M)]
    exact component_dimension_le L R _

attribute [local instance] RingHomInvPair.of_ringEquiv

theorem secondInflation_dimension_eq (M : ModuleCat.{v} R) :
    projectiveDimension ((secondInflation L R).obj M) = projectiveDimension M := by
  rw [← ModuleCat.projectiveDimension_eq_of_semiLinearEquiv
    (RingEquiv.prodComm : R × L ≃+* L × R) (swapInflationEquiv L R M)]
  exact firstInflation_dimension_eq R L M

def swapEquiv (M : ModuleCat.{v} (L × R)) :
    swapModule L R M ≃ₛₗ[RingHomClass.toRingHom (RingEquiv.prodComm : R × L ≃+* L × R)] M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem second_component_dimension_le (M : ModuleCat.{v} (L × R)) :
    projectiveDimension (secondObject L R M) ≤ projectiveDimension M := by
  rw [← ModuleCat.projectiveDimension_eq_of_semiLinearEquiv
    (RingEquiv.prodComm : R × L ≃+* L × R) (swapEquiv L R M)]
  exact component_dimension_le R L _

theorem product_dimension_eq_sup (M : ModuleCat.{v} (L × R)) :
    projectiveDimension M = projectiveDimension (firstObject L R M) ⊔
      projectiveDimension (secondObject L R M) := by
  apply le_antisymm
  · refine le_of_forall_ge (fun d hd => ?_)
    obtain ⟨hL,hR⟩ := sup_le_iff.mp hd
    induction d with
    | bot =>
      have zL := (projectiveDimension_eq_bot_iff _).mp (le_bot_iff.mp hL)
      have zR := (projectiveDimension_eq_bot_iff _).mp (le_bot_iff.mp hR)
      rw [ModuleCat.isZero_iff_subsingleton] at zL zR
      letI := zL
      letI := zR
      apply le_of_eq
      apply (projectiveDimension_eq_bot_iff M).mpr
      rw [ModuleCat.isZero_iff_subsingleton]
      apply (splitting L R M).subsingleton_congr.mpr
      exact ⟨fun x y => Prod.ext
        (Subsingleton.elim (show firstObject L R M from x.1) y.1)
        (Subsingleton.elim (show secondObject L R M from x.2) y.2)⟩
    | coe d =>
      induction d with
      | top => exact le_top
      | coe n =>
        have : HasProjectiveDimensionLE (firstObject L R M) n :=
          (projectiveDimension_le_iff _ n).mp hL
        have : HasProjectiveDimensionLE (secondObject L R M) n :=
          (projectiveDimension_le_iff _ n).mp hR
        have := firstInflation_dimensionLE L R n (firstObject L R M)
        have := secondInflation_dimensionLE L R n (secondObject L R M)
        let e := ModuleCat.biprodIsoProd ((firstInflation L R).obj (firstObject L R M))
          ((secondInflation L R).obj (secondObject L R M))
        have : HasProjectiveDimensionLT (pairObject L R M) (n+1) :=
          hasProjectiveDimensionLT_of_iso e (n+1)
        have : HasProjectiveDimensionLT M (n+1) :=
          hasProjectiveDimensionLT_of_iso (splitting L R M).toModuleIso.symm (n+1)
        exact (projectiveDimension_le_iff _ n).mpr inferInstance
  · exact sup_le (component_dimension_le L R M) (second_component_dimension_le L R M)

abbrev inflatedPair (M : ModuleCat.{v} L) (N : ModuleCat.{v} R) :
    ModuleCat.{v} (L × R) := ModuleCat.of (L × R)
      (((firstInflation L R).obj M) × ((secondInflation L R).obj N))

local instance firstPairScalarModule (M : ModuleCat.{v} L) (N : ModuleCat.{v} R) :
    Module L (firstSpace L R (inflatedPair L R M N)) :=
  firstModule L R (inflatedPair L R M N)

def firstPairEquiv (M : ModuleCat.{v} L) (N : ModuleCat.{v} R) :
    firstSpace L R (inflatedPair L R M N) ≃ₗ[L] M where
  toFun x := x.val.1
  invFun x := ⟨(x,0), by
    change ((1 : L) • x, (0 : R) • (0 : N)) = (x,0)
    simp⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have h := congrArg Prod.snd x.property
      change (0 : R) • x.val.2 = x.val.2 at h
      simpa only [zero_smul] using h
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def secondPairEquiv (M : ModuleCat.{v} L) (N : ModuleCat.{v} R) :
    secondObject L R (inflatedPair L R M N) ≃ₗ[R] N where
  toFun x := x.val.2
  invFun x := ⟨(0,x), by
    change ((0 : L) • (0 : M), (1 : R) • x) = (0,x)
    simp⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · have h := congrArg Prod.fst x.property
      change (0 : L) • x.val.1 = x.val.1 at h
      simpa only [zero_smul] using h
    · rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual two-block inflated module has the maximum of its two original
projective dimensions; no finite-dimension or nonzero hypotheses are needed. -/
theorem inflatedPair_dimension_eq_sup (M : ModuleCat.{v} L) (N : ModuleCat.{v} R) :
    projectiveDimension (inflatedPair L R M N) = projectiveDimension M ⊔ projectiveDimension N := by
  rw [product_dimension_eq_sup L R]
  exact congrArg₂ (fun a b => a ⊔ b)
    (ModuleCat.projectiveDimension_eq_of_linearEquiv (firstPairEquiv L R M N))
    (ModuleCat.projectiveDimension_eq_of_linearEquiv (secondPairEquiv L R M N))

end
end Note198.ProductProjectiveDimension
