structure Graph (E : Type u) (V : Type v) where
  s : E → V
  t : E → V

structure GraphHom (g₁ : Graph E₁ V₁) (g₂ : Graph E₂ V₂) where
  mapE : E₁ → E₂
  mapV : V₁ → V₂
  sourceCompliant (e : E₁) : (g₂.s (mapE e)) = mapV (g₁.s e)
  targetCompliant (e : E₁) : (g₂.t (mapE e)) = mapV (g₁.t e)


def Adj (g : Graph E V) (a b : V) : Prop :=
  ∃ e : E, g.s e = a ∧ g.t e = b

def GraphPath (g : Graph E V) (path : List V) : Prop :=
  match path with
    | a :: b :: tl => (Adj g a b) ∧ GraphPath g (b :: tl)
    | _ => true

def AcyclicGraph (g : Graph E V) : Prop :=
  ∀ (e : List V), GraphPath g e →
    match e with
    | [] => True
    | h :: t => ∀ x ∈ t, x ≠ h

structure Hypergraph (E : Type u) (V : Type v) where
  s : E → List V
  t : E → List V

def DiscreteHyperGraphs (V : Type v) : Type _ :=
  Hypergraph Empty V

def HAdj (hg : Hypergraph E V) (a b : List V) : Prop :=
  ∃ e : E, hg.s e = a ∧ hg.t e = b

def HGraphPath (hg : Hypergraph E V) (path : List (List V)) : Prop :=
  match path with
    | a :: b :: tl => (HAdj hg a b) ∧ (HGraphPath hg (b :: tl))
    | _ => True

def AcyclicHyperGraph (hg : Hypergraph E V) : Prop :=
  ∀ (e : List (List V)), HGraphPath hg e →
  match e with
  | [] => True
  | hd :: tl => ∀ x ∈ tl, x ≠ hd

def Hypergraph.toGraph (hg : Hypergraph E V) : Graph E (List V) :=
  { s := hg.s,
    t := hg.t }

def Graph.toHypergraph (g : Graph E (List V)) : Hypergraph E V :=
  { s := g.s,
    t := g.t }

@[simp]
theorem hadj_iff_adj (hg : Hypergraph E V) (a b : List V) :
    HAdj hg a b ↔ Adj hg.toGraph a b :=
  Iff.rfl

@[simp]
theorem hgraphPath_iff_graphPath (hg : Hypergraph E V) (path : List (List V)) :
    HGraphPath hg path ↔ GraphPath hg.toGraph path := by
  induction path with
  | nil => simp [HGraphPath, GraphPath]
  | cons hd tl ih =>
    cases tl with
    | nil => simp [HGraphPath, GraphPath]
    | cons b rest =>
      dsimp [HGraphPath, GraphPath]
      rw [ih]
      rfl

@[simp]
theorem acyclicHyperGraph_iff_acyclicGraph (hg : Hypergraph E V) :
    AcyclicHyperGraph hg ↔ AcyclicGraph hg.toGraph := by
  constructor
  · intro h e he
    have he' : HGraphPath hg e := (hgraphPath_iff_graphPath hg e).mpr he
    have h_eval := h e he'
    cases e with
    | nil => trivial
    | cons hd tl => exact h_eval
  · intro h e he
    have he' : GraphPath hg.toGraph e := (hgraphPath_iff_graphPath hg e).mp he
    have h_eval := h e he'
    cases e with
    | nil => trivial
    | cons hd tl => exact h_eval

inductive DAG (V : Type) : List V → Type
  | empty : DAG V []
  | add (v : V) {vs : List V} (prev : DAG V vs)
        (h_new : v ∉ vs)
        (edges : List V) (h_edges : ∀ e ∈ edges, e ∈ vs) : DAG V (v :: vs)

def DAGEdges {A : Type} {nodes : List A} (g : DAG A nodes) : Type :=
  match g with
  | .empty => Empty
  | .add _ prev _ edges _ =>
      Sum (DAGEdges prev) (Fin edges.length)

def DAGSource {A : Type} {nodes : List A} (d : DAG A nodes) : DAGEdges d → A :=
  match d with
  | .empty => fun e => nomatch e
  | .add v prev _ _ _ => fun e =>
      match e with
      | Sum.inr _ => v
      | Sum.inl old_edge => DAGSource prev old_edge

def DAGTarget {A : Type} {nodes : List A} (d : DAG A nodes) : DAGEdges d → A :=
  match d with
  | .empty => fun e => nomatch e
  | .add _ prev _ edges _ => fun e =>
    match e with
    | Sum.inr new_edge => edges[new_edge]
    | Sum.inl old_edge => DAGTarget prev old_edge

def DAGtoGraph {A : Type} {nodes : List A} (d : DAG A nodes) : Graph (DAGEdges d) A :=
  { s := DAGSource d,
    t := DAGTarget d }

theorem dag_source_mem {A : Type} {nodes : List A} (d : DAG A nodes) (e : DAGEdges d) :
    DAGSource d e ∈ nodes := by
  induction d with
  | empty => nomatch e
  | add v prev _ edges _ ih =>
    cases e with
    | inr _ =>
      dsimp [DAGSource]
      exact List.Mem.head _
    | inl old_edge =>
      dsimp [DAGSource]
      exact List.Mem.tail v (ih old_edge)

theorem dag_target_mem {A : Type} {nodes : List A} (d : DAG A nodes) (e : DAGEdges d) :
    DAGTarget d e ∈ nodes := by
  induction d with
  | empty => nomatch e
  | add v prev _ edges h_edges ih =>
    cases e with
    | inr new_edge =>
      dsimp [DAGTarget]
      exact List.Mem.tail v (h_edges _ (List.getElem_mem new_edge.2))
    | inl old_edge =>
      dsimp [DAGTarget]
      exact List.Mem.tail v (ih old_edge)

def DAG.toTightGraph {A : Type} {nodes : List A} (d : DAG A nodes) :
    Graph (DAGEdges d) { v : A // v ∈ nodes } :=
  { s := fun e => ⟨DAGSource d e, dag_source_mem d e⟩,
    t := fun e => ⟨DAGTarget d e, dag_target_mem d e⟩ }

theorem dag_add_target_mem {A : Type} {nodes : List A}
  (v : A) (prev : DAG A nodes) (h_new : v ∉ nodes)
  (edges : List A) (h_edges : ∀ e ∈ edges, e ∈ nodes)
  (e : DAGEdges (DAG.add v prev h_new edges h_edges)) :
  DAGTarget (DAG.add v prev h_new edges h_edges) e ∈ nodes := by
  cases e with
  | inr new_edge =>
    dsimp [DAGTarget]
    exact h_edges _ (List.getElem_mem new_edge.2)
  | inl old_edge =>
    dsimp [DAGTarget]
    exact dag_target_mem prev old_edge

theorem dag_add_adj_target_mem {A : Type} {nodes : List A}
  (v : A) (prev : DAG A nodes) (h_new : v ∉ nodes)
  (edges : List A) (h_edges : ∀ e ∈ edges, e ∈ nodes)
  (x y : A) (h_adj : Adj (DAGtoGraph (DAG.add v prev h_new edges h_edges)) x y) :
  y ∈ nodes := by
  rcases h_adj with ⟨e, _, ht⟩
  have ht_mem := dag_add_target_mem v prev h_new edges h_edges e
  exact ht ▸ ht_mem

theorem dag_add_path_tail_mem {A : Type} {nodes : List A}
  (v : A) (prev : DAG A nodes) (h_new : v ∉ nodes)
  (edges : List A) (h_edges : ∀ e ∈ edges, e ∈ nodes) :
  ∀ (rest : List A) (a : A),
    GraphPath (DAGtoGraph (DAG.add v prev h_new edges h_edges)) (a :: rest) →
    ∀ x ∈ rest, x ∈ nodes := by
  intro rest
  induction rest with
  | nil =>
    intro _ _ x hx
    cases hx
  | cons b tl ih =>
    intro a hp x hx
    cases hx with
    | head =>
      have h_adj : Adj (DAGtoGraph (DAG.add v prev h_new edges h_edges)) a b := hp.1
      exact dag_add_adj_target_mem v prev h_new edges h_edges a b h_adj
    | tail _ hx_tl =>
      have hp_rest : GraphPath (DAGtoGraph (DAG.add v prev h_new edges h_edges)) (b :: tl) := hp.2
      exact ih b hp_rest x hx_tl

theorem graph_path_add_to_prev {A : Type} {nodes : List A}
  (v : A) (prev : DAG A nodes) (h_new : v ∉ nodes)
  (edges : List A) (h_edges : ∀ e ∈ edges, e ∈ nodes) :
  ∀ (p : List A), (∀ x ∈ p, x ∈ nodes) →
    GraphPath (DAGtoGraph (DAG.add v prev h_new edges h_edges)) p →
    GraphPath (DAGtoGraph prev) p := by
  intro p
  match p with
  | [] => intro _ _; trivial
  | [_] => intro _ _; trivial
  | x :: y :: rest =>
    intro h_nodes hp
    have h_adj := hp.1
    have hp_tail := hp.2
    rcases h_adj with ⟨e, hs, ht⟩
    cases e with
    | inr new_edge =>
      dsimp [DAGtoGraph, DAGSource] at hs
      have hx : x ∈ nodes := h_nodes x (List.Mem.head _)
      have h_contra : v ∈ nodes := hs ▸ hx
      exact (h_new h_contra).elim
    | inl old_edge =>
      dsimp [DAGtoGraph, DAGSource, DAGTarget] at hs ht
      have h_adj_prev : Adj (DAGtoGraph prev) x y := ⟨old_edge, hs, ht⟩
      have h_tail_nodes : ∀ z ∈ (y :: rest), z ∈ nodes := fun z hz => h_nodes z (List.Mem.tail x hz)
      have h_tail_prev := graph_path_add_to_prev v prev h_new edges h_edges (y :: rest) h_tail_nodes hp_tail
      exact ⟨h_adj_prev, h_tail_prev⟩

-- The trivial empty-path case.
-- (You often don't even need to write this lemma, since `simp` or `intro _; trivial`
-- can instantly prove the `[]` case in your main proof).
theorem path_cases_nil {A : Type} {nodes : List A}
  (v : A) (prev : DAG A nodes) (h_new : v ∉ nodes)
  (edges : List A) (h_edges : ∀ e ∈ edges, e ∈ nodes) :
  GraphPath (DAGtoGraph (DAG.add v prev h_new edges h_edges)) [] → True := by
    intro _
    trivial

-- The core invariant for any path with at least one node.
-- Notice how clean the tactic state will be: no matches, just explicit variables `h` and `t`.
theorem path_cases_step {A : Type} {nodes : List A}
  (v : A) (prev : DAG A nodes) (h_new : v ∉ nodes)
  (edges : List A) (h_edges : ∀ e ∈ edges, e ∈ nodes)
  (a b : A) (tl : List A) :
  GraphPath (DAGtoGraph (DAG.add v prev h_new edges h_edges)) (a :: b :: tl) →
  (a = v ∧ ∀ x ∈ (b :: tl), x ∈ nodes) ∨
  (a ∈ nodes ∧ GraphPath (DAGtoGraph prev) (a :: b :: tl) ∧ ∀ x ∈ (b :: tl), x ∈ nodes) := by
    intro path
    rcases path with ⟨h_adj, h_rest⟩
    have h_tail_nodes := dag_add_path_tail_mem v prev h_new edges h_edges (b :: tl) a ⟨h_adj, h_rest⟩
    have h_adj_copy := h_adj
    unfold Adj at h_adj
    rcases h_adj with ⟨e, hs, ht⟩
    cases e with
    | inr new_edge =>
      dsimp [DAGtoGraph, DAGSource, DAGTarget] at hs ht
      left
      exact ⟨hs.symm, h_tail_nodes⟩
    | inl prev_edge =>
      dsimp [DAGtoGraph, DAGSource, DAGTarget] at hs ht
      right
      have ha_nodes : a ∈ nodes := by
        have := dag_source_mem prev prev_edge
        exact hs ▸ this
      have h_all_nodes : ∀ x ∈ (a :: b :: tl), x ∈ nodes := by
        intro x hx
        cases hx with
        | head => exact ha_nodes
        | tail _ hx_tl => exact h_tail_nodes x hx_tl
      have hp_prev := graph_path_add_to_prev v prev h_new edges h_edges (a :: b :: tl) h_all_nodes ⟨h_adj_copy, h_rest⟩
      exact ⟨ha_nodes, hp_prev, h_tail_nodes⟩

theorem dag_is_acyclic {A : Type} {nodes : List A} (d : DAG A nodes) :
  AcyclicGraph (DAGtoGraph d) := by
  -- We prove acyclicity by structural induction on the graph's construction
  induction d with
  -- Base Case: The empty graph
  | empty =>
    intro p hp
    cases p with
    | nil => trivial
    | cons h t =>
      cases t with
      | nil =>
        -- Path of length 1: ∀ x ∈ [], x ≠ h (vacuously true)
        intro x hx
        contradiction
      | cons x rest =>
        -- Path of length ≥ 2: Requires an edge, but DAGEdges empty is the `Empty` type.
        rcases hp.1 with ⟨e, _⟩
        exact nomatch e

  -- Inductive Step: Adding a new node
  | add v prev h_new edges h_edges ih =>
    rename_i vs
    intro p hp
    cases p with
    | nil => trivial
    | cons h t =>
      cases t with
      | nil =>
        intro x hx
        contradiction
      | cons b tl =>
        -- Evaluate our invariant lemma on the specific path `h :: b :: tl`
        have h_cases := path_cases_step v prev h_new edges h_edges h b tl hp

        cases h_cases with
        | inl h_left =>
          -- Case 1: The path starts at our newly added node `v`
          have h_eq : h = v := h_left.1
          have h_in : ∀ x ∈ (b :: tl), x ∈ vs := h_left.2

          -- We must prove no node in the rest of the path loops back to `h`
          intro x hx h_contra

          -- We know `x` is in the older nodes
          have x_in_vs : x ∈ vs := h_in x hx

          -- If x looped back to h, then x = v
          have x_is_v : x = v := by rw [h_contra, h_eq]

          -- But this contradicts our type's requirement that v ∉ nodes!
          rw [x_is_v] at x_in_vs
          exact h_new x_in_vs

        | inr h_right =>
          -- Case 2: The path belongs entirely to the older graph `prev`
          have hp_prev : GraphPath (DAGtoGraph prev) (h :: b :: tl) := h_right.2.1

          -- Because the path is completely contained in `prev`,
          -- we instantly win by applying the Inductive Hypothesis.
          exact ih (h :: b :: tl) hp_prev

def DAGtoHypergraph {V : Type} {nodes : List (List V)} (d : DAG (List V) nodes) : Hypergraph (DAGEdges d) V :=
  (DAGtoGraph d).toHypergraph

theorem dag_to_hypergraph_is_acyclic {V : Type} {nodes : List (List V)} (d : DAG (List V) nodes) :
    AcyclicHyperGraph (DAGtoHypergraph d) := by
  rw [acyclicHyperGraph_iff_acyclicGraph]
  exact dag_is_acyclic d
