import .defs
import .cofinite
-- TODO : Replace these names with the fully-qualified names

/-!

Sufficiently nice maps between graphs induce maps between connected components.
In other words, there is a functor from the category of simple graphs with appropriate morphisms
to the category of sets, taking each graph to its set of connected components.

The required maps between graphs are cofinite (maps that pull back finite sets to finite sets) 
weak homomorphisms (maps that send reachable pairs of points to reachable pairs of points).

-/

variables {V V' V'' : Type*}
variables {G : simple_graph V} {G' : simple_graph V'} {G'' : simple_graph V''}

/-- A *weak homomorphism* is a map between simple graphs that sends 
  reachable pairs of points to reachable pairs of points. -/
abbreviation weak_hom  (G : simple_graph V) (G' : simple_graph V') := 
  rel_hom G.reachable G'.reachable

/-- A map between graphs that preserves reachability. -/
abbreviation reachable_hom  (G : simple_graph V) (G' : simple_graph V') (φ : V → V') :=
  ∀ {u v : V}, G.reachable u v → G'.reachable (φ u) (φ v)

namespace weak_hom

infix ` ↝g `:50 := weak_hom -- type as `\r~`

lemma map_reachable 
  (φ : G ↝g G') : reachable_hom G G' φ :=
    λ _ _, φ.map_rel

def from_hom (φ : G →g G') : G ↝g G' :=
  ⟨φ, λ {a} {b}, sorry⟩ -- TODO `reachable.map φ` works in a newer version of `mathlib`

def component_map (φ : G ↝g G') (C : G.connected_component) : G'.connected_component :=
  C.lift (λ v, simple_graph.connected_component_mk G' (φ v))
    ( λ _ _ p _, 
       simple_graph.connected_component.eq.mpr
        (map_reachable φ (nonempty.intro p)) )

protected def id : G ↝g G := ⟨id, λ _ _, id⟩

def comp (φ : G ↝g G') (ψ : G' ↝g G'') : G ↝g G'' :=
  ⟨ψ ∘ φ, λ _ _, ψ.map_reachable ∘ φ.map_reachable⟩

end weak_hom

structure nice_map
    (G : simple_graph V) (G' : simple_graph V')
    (φ : V → V') :=
  (finset_mapping : finset V' → finset V)
  (finset_inv_sub : ∀ L : finset V', φ⁻¹' L ⊆ finset_mapping L)
  (induced_reachable_hom : ∀ L : finset V', 
    reachable_hom (G.out $ finset_mapping L) (G'.out L) 
    (induce_out φ (finset_inv_sub L)))

def nice_map.cofinite (φ : V → V') 
  {G : simple_graph V} {G' : simple_graph V'} 
  (hφ_nice : nice_map G G' φ) : cofinite φ :=
begin
  intro v,
  let L : finset V'  := {v},
  let K := hφ_nice.finset_mapping L,
  have : φ ⁻¹' ↑L ⊆ ↑K := hφ_nice.finset_inv_sub L,
  -- apply set.finite.subset,
  -- exact finset.finite_to_set K,
  -- exact hφ_nice.finset_inv_sub {v},
  sorry
end

def nice_map.id : nice_map G G (id : V → V) := 
{ finset_mapping := id,
  finset_inv_sub := λ _ _, id,
  induced_reachable_hom := by {rintros _ ⟨_, _⟩ ⟨_, _⟩, exact id, } }

def nice_map.comp 
  (φ : V → V') (hφ_nice : nice_map G G' φ) 
  (ψ : V' → V'') (hψ_nice : nice_map G' G'' ψ) : nice_map G G'' (ψ ∘ φ) := 
{ finset_mapping := hφ_nice.finset_mapping ∘ hψ_nice.finset_mapping,
  finset_inv_sub := by {
    intro M,
    let L := cofinite.preimage (nice_map.cofinite ψ hψ_nice) M,
    simp, rw [set.preimage_comp],
    sorry
  },
  induced_reachable_hom := by {
    rintros M ⟨_, _⟩ ⟨_, _⟩ hreach,
    simp [induce_out],
    sorry
  } } 

/-- The category with objects as simple graphs and morphisms as nice maps. -/
instance NiceGrph : category_theory.category Σ (V : Type*), simple_graph V := 
{ hom := λ ⟨V, G⟩ ⟨V', G'⟩, Σ φ : V → V', nice_map G G' φ,
  id := λ ⟨V, G⟩, ⟨id, nice_map.id⟩,
  comp := sorry,
  id_comp' := sorry,
  comp_id' := sorry,
  assoc' := sorry }

def functoriality {G : simple_graph V} {G' : simple_graph V'}
  (φ : V → V') (hφ_nice : nice_map G G' φ) : 
    G.end → G'.end :=
  λ ⟨ε, ε_sec⟩, ⟨λ L,
  (weak_hom.component_map
    ⟨_, λ {_} {_}, hφ_nice.induced_reachable_hom L⟩
    (ε _)
  ), by {intros L L' h, simp, sorry }⟩