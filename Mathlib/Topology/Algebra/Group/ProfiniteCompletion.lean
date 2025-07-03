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
    sorry

lemma CharcterizationOpenProfiniteCompletion (U : Set (ProfiniteCompletion G)) : (IsOpen U) ↔ (∀ (x : U), ∃ (V : FiniteOpenNormalSubgroup G), ∀ (y : ProfiniteCompletion G), (x.1.1 V = y.1 V) → (y ∈ U)) := by
  sorry

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

#check IsClosed

lemma kerIsTrivialIfProfiniteGroup -- ⨅  (U : FiniteOpenNormalSubgroup G) is trivial
  sorry

lemma Isom_Structuremorphism_when_profinite
  [CompactSpace G] [TotallyDisconnectedSpace G] [T2Space G] :
  Function.Bijective (StructureMorphism G) := by
  rw [Function.Bijective]
  constructor
  · --injective ker_StructureMorphism and ⨅  (U : FiniteOpenNormalSubgroup G) = 1
    sorry
  · -- surjectivity
    sorry
