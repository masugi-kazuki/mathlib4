import Mathlib

set_option autoImplicit false
variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

lemma quot_by_ON_discrete (U : OpenNormalSubgroup G)
    : DiscreteTopology (G ⧸ (U : Subgroup G)) := by
      infer_instance

structure FiniteOpenNormalSubgroup extends OpenNormalSubgroup G where
    finiteindex : toOpenNormalSubgroup.FiniteIndex

instance (U  : FiniteOpenNormalSubgroup G) : CompactSpace (G ⧸ U.1.1.1) := sorry

instance : Preorder (FiniteOpenNormalSubgroup G) where
  le := by
    intro U
    intro V
    exact U.1 ≤ V.1
  le_refl := by
    intro U
    simp
  le_trans := by
    intro U V W
    apply le_trans

open CategoryTheory

@[simps]
def Diag : (FiniteOpenNormalSubgroup G) ⥤ ProfiniteGrp where
  obj := by
    intro U
    exact (ProfiniteGrp.of (G ⧸ (U.1 : Subgroup G)))
  map := by
    intro U V
    intro f
    apply ProfiniteGrp.ofHom
    refine ⟨?_, ?_⟩
    · fapply QuotientGroup.map
      exact MonoidHom.id G
      simp only [Subgroup.comap_id, OpenSubgroup.toSubgroup_le]
      exact (leOfHom f)
    · fun_prop

  map_comp := by
    intro  U V W
    intro f g
    ext x
    simp
    obtain ⟨ y,rfl ⟩ := QuotientGroup.mk_surjective x
    rfl

noncomputable def ProfiniteCompletion := ProfiniteGrp.limitConePtAux (Diag G)

instance : CompactSpace (ProfiniteCompletion G) :=
  inferInstanceAs (CompactSpace (ProfiniteGrp.limitCone (Diag G)).pt)

instance : TotallyDisconnectedSpace (ProfiniteCompletion G) :=
  inferInstanceAs (TotallyDisconnectedSpace (ProfiniteGrp.limitCone (Diag G)).pt)

instance : T2Space (ProfiniteCompletion G) :=
  inferInstanceAs (T2Space (ProfiniteGrp.limitCone (Diag G)).pt)

--G → limit (G/U) structure morphism of profinite completion
lemma Mem_ProfiniteCompletion_iff (g : ∀ (U : FiniteOpenNormalSubgroup G), G ⧸ U.1.1.1) :
    g ∈ ProfiniteCompletion G ↔
      ∀ (U V: FiniteOpenNormalSubgroup G) (hUV : U.1 ≤ V.1),
        QuotientGroup.map _ _ (MonoidHom.id G) (by simpa) (g U)=(g V) := by
  sorry

 -- @[simps? toMonoidHom_apply_coe]
def StructureMorphism : G →ₜ* ProfiniteCompletion G where
  toFun := by
    intro g
    refine ⟨ ?_,?_ ⟩
    · intro _
      exact QuotientGroup.mk g
    · simp [Mem_ProfiniteCompletion_iff]
  map_one' := by
     rfl
  map_mul' := by
    intro g h
    dsimp
    ext U
    simp
  continuous_toFun := by
    fun_prop

lemma ker_StructureMorphism : MonoidHom.ker (StructureMorphism G).1 = ⨅  (U : FiniteOpenNormalSubgroup G), U.1.1.1 := by
  ext g
  simp [Subgroup.mem_iInf]
  constructor
  · intro h
    intro U
    rw [Subtype.ext_iff, funext_iff] at h
    specialize h U
    replace h : QuotientGroup.mk' _ g = 1 := h
    rwa [← MonoidHom.mem_ker,QuotientGroup.ker_mk'] at h
  · intro h
    ext U
    specialize h U
    show QuotientGroup.mk' _ g = 1
    rw [← MonoidHom.mem_ker,QuotientGroup.ker_mk']
    apply h

lemma density_StructureMorphism_image : Dense (Set.range (StructureMorphism G) ) := by
  unfold Dense
  intro x
  unfold closure
  unfold Set.sInter
  simp only [Diag_obj_toProfinite_toTop_carrier, Diag_obj_group, Set.sInf_eq_sInter, Set.mem_sInter,
    Set.mem_setOf_eq, and_imp]
  intro F
  intro IsClosed_F
  intro IsEnoughLarge_F
  have isOpen_compl : IsOpen (Fᶜ) := by
    exact IsClosed.isOpen_compl

  -- Use the characterization lemma on Fᶜ, then use classical logic to deduce the property for F
  have h_char := CharcterizationOpenProfiniteCompletion G (Fᶜ)
  rw [h_char] at isOpen_compl
  -- Now isOpen_compl : ∀ (x : Fᶜ), ∃ (V : FiniteOpenNormalSubgroup G), ∀ (y : ProfiniteCompletion G), ↑↑x V = ↑y V → y ∈ Fᶜ
  -- Use by_contra to prove x ∈ F
  by_contra hx
  -- So x ∈ Fᶜ
  specialize isOpen_compl ⟨x, hx⟩
  rcases isOpen_compl with ⟨V, hV⟩
  -- Use density of the image to find y in the image of StructureMorphism G close to x
  -- (details omitted, proof continues...)
  simp at hV
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (x.1 V)
  specialize hV (fun W => QuotientGroup.mk' W.1.1.1 y)
  simp [hy] at hV
  apply hV
  apply IsEnoughLarge_F
  simp

  sorry

lemma OpenSubgrupInProfiniteIsOfFiniteIndex [CompactSpace G] [TotallyDisconnectedSpace G] [T2Space G] : ∀ (U : OpenNormalSubgroup G), U.FiniteIndex := sorry


lemma kerIsTrivialIfProfiniteGroup  [CompactSpace G] [TotallyDisconnectedSpace G] [T2Space G] :
 ⨅ (U : FiniteOpenNormalSubgroup G) ,U.1.1.1 = ⊥ := by
-- ⨅  (U : FiniteOpenNormalSubgroup G) is trivial
  apply Subgroup.ext
  intro g
  rw [Subgroup.mem_iInf, Subgroup.mem_bot]
  constructor
  intro hg
  by_contra hg_ne
  rcases t2_separation (ne_comm.mp hg_ne) with ⟨V, W, hV_open, hW_open, h1V, hgW, hVW_disj⟩
  obtain ⟨ U, hu ⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV_open h1V 
  by_cases h_gu : g ∈ U
  · unfold Disjoint at hVW_disj
    have hv := hu h_gu
    have h_ : {g} ≤ V := by simp [hv]
    have hg2 := hVW_disj h_
    simp at hg2
    contradiction
  · apply h_gu
    have : U.FiniteIndex := by
      exact OpenSubgrupInProfiniteIsOfFiniteIndex G U
    let U' : FiniteOpenNormalSubgroup G := ⟨ U , this ⟩ 
    exact hg U'


lemma Isom_Structuremorphism_when_profinite
  [CompactSpace G] [TotallyDisconnectedSpace G] [T2Space G] :
  Function.Bijective (StructureMorphism G) := by
  rw [Function.Bijective]
  constructor
  · -- injective
    apply (MonoidHom.ker_eq_bot_iff (StructureMorphism G).1).mp
    rw [ker_StructureMorphism G] -- Ker= ⨅  (U : FiniteOpenNormalSubgroup G)
    apply kerIsTrivialIfProfiniteGroup -- ⨅  (U : FiniteOpenNormalSubgroup G) is trivial
  · -- surjectivity
    rw [← Set.range_eq_univ]
    have : IsClosed (Set.range (StructureMorphism G)) := by
      apply IsCompact.isClosed
      exact isCompact_range (StructureMorphism G).continuous_toFun
    rw [← IsClosed.closure_eq this]
    refine denseRange_iff_closure_range.mp ?_
    apply density_StructureMorphism_image



def ProfiniteCompletion_map (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (f : G →ₜ* H) :
    (ProfiniteCompletion G) →ₜ* (ProfiniteCompletion H) where
      toFun := by
        intro g
        refine ⟨ ?_,?_ ⟩
        · intro U
          dsimp
          let V : FiniteOpenNormalSubgroup G := by
            refine ⟨ ⟨ U.comap f f.2 , ?_⟩, ?_⟩
            simp
            exact Subgroup.normal_comap _
            have : U.1.1.1.comap f = MonoidHom.ker ((QuotientGroup.mk' U.1.1.1).comp f.1) :=sorry
            dsimp []
            rw [this]
            have : Finite (H⧸U.1.1.1) := by
              rw [← Subgroup.finiteIndex_iff_finite_quotient]
              exact U.2
            apply Subgroup.finiteIndex_ker
          sorry
        · simp [Mem_ProfiniteCompletion_iff]
      map_one' := by
        rfl
      map_mul' := by
        intro g h
        dsimp
        ext U
        simp
      continuous_toFun := by
        fun_prop



lemma Univ_ProfiniteCompletion (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (f : G →ₜ* H) :
    ∃! (f' : (ProfiniteCompletion G) →ₜ* (ProfiniteCompletion H)),
    f'.comp (StructureMorphism G) = (StructureMorphism H).comp f := by
  refine ⟨?_, ?_, ?_⟩
  ·sorry
  ·sorry
  ·sorry
