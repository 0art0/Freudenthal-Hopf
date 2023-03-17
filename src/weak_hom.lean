import combinatorics.simple_graph.connectivity

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