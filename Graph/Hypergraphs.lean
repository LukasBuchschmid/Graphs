

structure Graph (E : Type u) (V : Type v) where
  s : E → V
  t : E → V

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
  | .add v prev h_new edges h_edges => fun e =>
      match e with
      | Sum.inr new_edge => v
      | Sum.inl old_edge => DAGSource prev old_edge


def DAGTarget {A : Type} {nodes : List A} (d : DAG A nodes) : DAGEdges d → A :=
  match d with
  | .empty => fun e => nomatch e
  | .add v prev h_new edges h_edges => fun e =>
    match e with
    | Sum.inr new_edge =>  edges[new_edge]
    | Sum.inl old_edge => DAGTarget prev old_edge


def DAGtoGraph {A : Type} {nodes : List A} (d : DAG A nodes) : Graph (DAGEdges d) A :=
  { s := DAGSource d,
    t := DAGTarget d }



-- The trivial empty-path case.
-- (You often don't even need to write this lemma, since `simp` or `intro _; trivial`
-- can instantly prove the `[]` case in your main proof).
theorem path_cases_nil {A : Type} {nodes : List A}
  (v : A) (prev : DAG A nodes) (h_new : v ∉ nodes)
  (edges : List A) (h_edges : ∀ e ∈ edges, e ∈ nodes) :
  GraphPath (DAGtoGraph (DAG.add v prev h_new edges h_edges)) [] → True := by
    intro t
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
    unfold Adj at h_adj
    rcases h_adj with ⟨e, hs, ht⟩
    cases e with
    | inl prev_edge => sorry
    | inr new_edge =>
      dsimp [DAGtoGraph, DAGSource, DAGTarget] at hs ht









  -- Now `path` automatically unfolds into `Adj ... a b ∧ GraphPath ... (b :: tl)`!



      -- Here you will unfold GraphPath and handle the edge constructors


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
        sorry

  -- Inductive Step: Adding a new node
  | add v prev h_new edges h_edges ih =>
    intro p hp
    cases p with
    | nil => trivial
    | cons h t =>

      -- Evaluate our invariant lemma on the specific path `h :: t`
      have h_cases := path_cases_step v prev h_new edges h_edges (h :: t) hp

      cases h_cases with
      | inl h_left =>
        -- Case 1: The path starts at our newly added node `v`
        have h_eq : h = v := h_left.1
        have h_in : ∀ x ∈ t, x ∈ nodes := h_left.2

        -- We must prove no node in the rest of the path loops back to `h`
        intro x hx h_contra

        -- We know `x` is in the older nodes
        have x_in_nodes : x ∈ nodes := h_in x hx

        -- If x looped back to h, then x = v
        have x_is_v : x = v := by rw [h_contra, h_eq]

        -- But this contradicts our type's requirement that v ∉ nodes!
        rw [x_is_v] at x_in_nodes
        exact h_new x_in_nodes

      | inr h_right =>
        -- Case 2: The path belongs entirely to the older graph `prev`
        have hp_prev : GraphPath (DAGtoGraph prev) (h :: t) := h_right.2.1

        -- Because the path is completely contained in `prev`,
        -- we instantly win by applying the Inductive Hypothesis.
        exact ih (h :: t) hp_prev
