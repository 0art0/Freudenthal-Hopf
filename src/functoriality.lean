import .defs
import .metric
import data.enat.basic
import tactic.basic

universes u v w

variables {V V' V'' : Type u} (G : simple_graph V) (G' : simple_graph V') (G'' : simple_graph V'')

open simple_graph

@[reducible]
def coarse_lipschitz_with (K : ℕ∞) (C : ℕ) (f : V → V') :=
  ∀ ⦃x y : V⦄, ∀ ⦃a : ℕ∞⦄, G.edist x y < a → G'.edist (f x) (f y) < K * a + C

def coarse_equal_with (K : ℕ∞) (f g : V → V'):=
  ∀ x : V, G'.edist (f x) (g x) < K

namespace coarse_lipschitz

variables {G} {G'}

-- can be derived from `hom`
protected theorem id : coarse_lipschitz_with G G 1 0 id := by {
  simp [coarse_lipschitz_with],
}

theorem hom (φ : G →g G') : coarse_lipschitz_with G G' 1 0 φ := by {
  intros x y a h,
  cases le_iff_lt_or_eq.mp (simple_graph.hom.edist_le φ x y) with 
    hedist_lt hedist_eq,
  { simp only [one_mul, algebra_map.coe_zero, add_zero],
    exact lt_trans hedist_lt h, },
  { simp only [h, hedist_eq, one_mul, algebra_map.coe_zero, add_zero], }}

theorem mono {f : V → V'} {K K' : ℕ∞} {C C' : ℕ} (hK : K ≤ K') (hC : C ≤ C')
  (hf : coarse_lipschitz_with G G' K C f)
  : coarse_lipschitz_with G G' K' C' f := by {
    rw [coarse_lipschitz_with],
    intros x y a hdist,
    refine lt_of_le_of_lt' _ (hf hdist),
    exact add_le_add (enat.mul_right_le hK) (with_top.coe_mono hC),
  }

theorem comp (f : V → V') (g : V' → V'')
  {K K' : ℕ∞} {C C' : ℕ}
  (hf : coarse_lipschitz_with G G' K C f) (hg : coarse_lipschitz_with G' G'' K' C' g)
  : coarse_lipschitz_with G G'' (K' * K) (K'.to_nat * C + C') (g ∘ f) := by {
    intros _ _ a hdist,
    refine lt_of_le_of_lt' _ (hg (hf hdist)),
    rw [enat.coe_add, ← add_assoc, mul_add, ← mul_assoc, enat.coe_mul],
    refine add_le_add _ (le_refl _),
    by_cases h : K' = ⊤,
    { subst h,
      simp only [enat.top_mul_left, enat.top_add_left, top_le_iff], },
    { rw [(enat.coe_to_nat_eq_self).mpr h],
      exact le_refl _, }
  }

def infty_wlog {P : (V → V') → Sort*} (C : ℕ) :
  (∀ (f : V → V') (hf : coarse_lipschitz_with G G' ⊤ C f), P f) →
  (∀ (f : V → V') (K : ℕ∞) (hf : coarse_lipschitz_with G G' K C f), P f) :=
begin
  intros h f K hf,
  apply h,
  exact mono le_top (le_refl _) hf,
end

theorem infty_iff (f : V → V') {C : ℕ} :
  (coarse_lipschitz_with G G' ⊤ C f) ↔ (∀ x y : V, G.reachable x y → G'.reachable (f x) (f y)) := by {
    have : ∀ (K : ℕ∞) (n : ℕ), ⊤ * K + n = ⊤ := by {
      intros K n,
      sorry -- needs missing `enat` lemmas
      },
    simp_rw [simple_graph.reachable_iff_edist_ne_top,
      coarse_lipschitz_with, this],
    sorry -- should be easy enough from here
  }

def out_restrict {f : V → V'} {k : ℕ∞} {c : ℕ} (hf : coarse_lipschitz_with G G' k c f) (K : set V) :
  coarse_lipschitz_with (G.out K) G' k c (f ∘ subtype.val) := by {
    intros x y a h,
    apply hf,
    sorry, -- can be proved using the fact that `subtype.val` is a homomorphism
  }

-- the "relative" version of `out`
def out'_restrict {K K' : set V} (h : K ⊆ K') {f : ↥(K)ᶜ → V'} {k : ℕ∞} {c : ℕ}
  (hf : coarse_lipschitz_with (G.out K) G' k c f) :
    coarse_lipschitz_with (G.out K') G' k c (f ∘ (simple_graph.out_hom G h).to_fun) := by {
      intros x y a h,
      apply hf,
      sorry -- should follow from transitivity
    }

def expand_out {L L' : set V'} (h : L ⊆ L') {f : V → ↥L'ᶜ} {k : ℕ∞} {c : ℕ}
  (hf : coarse_lipschitz_with G (G'.out L') k c f) :
  coarse_lipschitz_with G (G'.out L) k c ((induce_out id h) ∘ f) :=
  -- TODO maybe replace `induce_out id h`
    by {
      intros _ _ a h,
      have := hf h,
      all_goals {sorry}, -- will follow from the fact that `induce_out id h` is a homomorphism
    }

def comp_map {f : V → V'} {k : ℕ∞} {c : ℕ} (hf : coarse_lipschitz_with G G' k c f) :
  G.connected_component → G'.connected_component :=
    simple_graph.connected_component.lift (λ v, G'.connected_component_mk (f v)) (by {
      intros _ _ p _,
      rw simple_graph.connected_component.eq,
      apply (infty_iff f).mp,
      refine mono _ (nat.le_refl c) hf,
      sorry{exact le_top}, -- not working for some reason
      exact nonempty.intro p, })

-- this could potentially be stated better using an "absolute" rather than a "relative" perspective
theorem up_comp {K K' : set V} (h : K ⊆ K') {f : ↥(K)ᶜ → V'} {k : ℕ∞} {c : ℕ}
  (hf : coarse_lipschitz_with (G.out K) G' k c f) (C : G.comp_out K') :
    comp_map hf (C.hom h) = comp_map (out'_restrict h hf) C := by {
      refine C.ind _,
      intros _ _,
      dsimp [comp_out.hom, connected_component.map, comp_map],
      congr, }

theorem comp_down {L L' : finset V'} (h : L ⊆ L') {f : V → ↥(↑L')ᶜ} {k : ℕ∞} {c : ℕ}
  (hf : coarse_lipschitz_with G (G'.out L') k c f) {C : G.connected_component} :
    comp_out.hom h (comp_map hf C) = (comp_map (expand_out h hf) C) := by {
      refine C.ind _,
      intro _,
      dsimp [comp_out.hom, connected_component.map, comp_map],
      congr,
      apply subtype.eq,
      simp, }

end coarse_lipschitz

-- set_option trace.class_instances true

/-- The kind of map between graphs which induces a map on the ends. -/
structure coarse_map {V V' : Type u} (G : simple_graph V) (G' : simple_graph V') (φ : V → V') :=
  (κ : ℕ∞) (C : ℕ)
  (finset_mapping : finset V' → finset V)
  (finset_inv_sub : ∀ L : finset V', φ ⁻¹' (L : set V') ⊆ (finset_mapping L : set V))
  (induced_coarse_lipschitz : ∀ L : finset V',
    coarse_lipschitz_with (G.out $ finset_mapping L) (G'.out L)
      κ C (induce_out φ (finset_inv_sub L)))

-- TODO maybe there can be a parametrized structure "lifting" any property of homomorphisms
-- to its coarse version
structure coarse_close {V V' : Type u} (G : simple_graph V) (G' : simple_graph V') (f g : V → V') :=
  (κ : ℕ∞)
  (finset_mapping : finset V' → finset V)
  (finset_inv_subl : ∀ L : finset V', f ⁻¹' (L : set V') ⊆ (finset_mapping L : set V))
  (finset_inv_subr : ∀ L : finset V', g ⁻¹' (L : set V') ⊆ (finset_mapping L : set V))
  (induced_coarse_equal : ∀ L : finset V', coarse_equal_with (G'.out L) κ
    (induce_out f (finset_inv_subl L)) (induce_out g (finset_inv_subr L)))

variables {G} {G'}

-- TODO Move this to `defs`
lemma end_back {K K' : (finset V)ᵒᵖ} (h : K.unop ⊆ K'.unop) (e : G.end) :
  e.val K = (e.val K').hom h := by {
    symmetry,
    exact e.property (category_theory.op_hom_of_le h),  }

def coarse_map.end_map [decidable_eq V] {f : V → V'} (fcoarse : coarse_map G G' f) : G.end → G'.end := by
  {
    rintro e,
    refine ⟨λ L, _, _⟩,
    let comp_map := coarse_lipschitz.comp_map (fcoarse.induced_coarse_lipschitz L.unop),
    apply comp_map,
    let Gcomp := e.val (opposite.op $ fcoarse.finset_mapping L.unop),
    exact Gcomp,
    { intros L L' hLL',
      let K : (finset V)ᵒᵖ := opposite.op (
        (fcoarse.finset_mapping L.unop) ∪ (fcoarse.finset_mapping L'.unop)),
      have hL : (opposite.op $ fcoarse.finset_mapping L.unop).unop ⊆ K.unop := by {
        simp only [opposite.unop_op], apply finset.subset_union_left, },
      have hL' : (opposite.op $ fcoarse.finset_mapping L'.unop).unop ⊆ K.unop := by {
        simp only [opposite.unop_op], apply finset.subset_union_right, },
      dsimp,
      rw [← subtype.val_eq_coe,
      end_back hL e, end_back hL' e,
      coarse_lipschitz.up_comp, coarse_lipschitz.up_comp],
      dsimp [comp_out_functor],
      rw [coarse_lipschitz.comp_down],
      refl,
    },
  }

def coarse_close.left_coarse_map {f g : V → V'} (hclose : coarse_close G G' f g) : coarse_map G G' f := 
{ κ := hclose.κ,
  C := 0,
  finset_mapping := hclose.finset_mapping,
  finset_inv_sub := hclose.finset_inv_subl,
  induced_coarse_lipschitz := by {
    intro L,
    unfold coarse_lipschitz_with,
    have := hclose.induced_coarse_equal L,
    unfold coarse_equal_with at this,
    sorry -- seems impossible, more assumptions needed
  } }

def coarse_close.right_coarse_map {f g : V → V'} (hclose : coarse_close G G' f g) : coarse_map G G' g := sorry

private lemma well_separated (G : simple_graph V) (Gpc : G.preconnected) (K : finset V) (m : ℕ)
  (C : G.comp_out K)
  (c : V) (cC : c ∈ C) (c' : V) :
  c ∉ (G.closed_neighborhood K m) → G.edist c c' ≤ m → c' ∈ C :=
begin
  rintro cnK,
  sorry,
/-rintro cnK,
  obtain ⟨w,wm⟩ := reachable.exists_walk_of_dist (Gpc c c'), rw ←wm,
  rintro hwm,
  have wdisK : disjoint (w.support.to_finset : set V) K, by {
    rw finset.disjoint_coe,
    by_contradiction h, rw finset.not_disjoint_iff at h,
    obtain ⟨x,xw,xK⟩ := h,
    rw [list.mem_to_finset,walk.mem_support_iff_exists_append] at xw,
    obtain ⟨cx,_,rfl⟩ := xw,
    apply cnK,
    dsimp only [thicken_],
    simp only [finite.mem_to_finset, mem_set_of_eq, exists_prop],
    use [x,xK],
    apply (dist_le cx).trans,
    refine le_trans _ hwm,
    simp only [length_append, le_add_iff_nonneg_right, zero_le'],},

  let Cw := comp_out.of_connected_disjoint (w.support.to_finset : set V) (connected.walk_support w) wdisK.symm,
  have : C = Cw, by
  { apply comp_out.eq_of_not_disjoint,
    rw set.not_disjoint_iff,
    use [c,cC],
    apply comp_out.of_connected_disjoint_sub,
    simp only [mem_coe, list.mem_to_finset, start_mem_support],},
  rw this,
  apply comp_out.of_connected_disjoint_sub,
  simp only [mem_coe, list.mem_to_finset, end_mem_support], -/
end


def coarse_equal.of_coarse_close [decidable_eq V] {f g : V → V'} {k : ℕ∞}
  (fcoarse : coarse_map G G' f) (gcoarse : coarse_map G G' g)
  (close : coarse_equal_with G' k f g)  : coarse_close G G' f g := 
  sorry -- TODO

def coarse_equal.end_equal [decidable_eq V] {f g : V → V'} {k : ℕ∞}
  (fcoarse : coarse_map G G' f) (gcoarse : coarse_map G G' g)
  (close : coarse_equal_with G' k f g) :
  coarse_map.end_map fcoarse = coarse_map.end_map gcoarse := by {
    dsimp [coarse_map.end_map],
    ext e L,
    dsimp,
    let K : (finset V)ᵒᵖ := opposite.op (
        (fcoarse.finset_mapping L.unop) ∪ (gcoarse.finset_mapping L.unop)),
    have hfL : (opposite.op $ fcoarse.finset_mapping L.unop).unop ⊆ K.unop := sorry,
    have hgL : (opposite.op $ gcoarse.finset_mapping L.unop).unop ⊆ K.unop := sorry,
    rw [← subtype.val_eq_coe,
    end_back hfL e, end_back hgL e,
    coarse_lipschitz.up_comp, coarse_lipschitz.up_comp],

    generalize : e.val K = C,
    refine C.ind _,
    intros v hv,
    dsimp [coarse_lipschitz.comp_map],
    rw [simple_graph.connected_component.eq, simple_graph.reachable_iff_edist_ne_top],
    dsimp [induce_out],
    have hyp := (coarse_equal.of_coarse_close fcoarse gcoarse close).induced_coarse_equal L.unop
      ⟨v, sorry⟩,
    dsimp [induce_out, coarse_equal_with] at hyp,
    sorry, -- need `coarse_close`, not just `coarse_equal`
  }