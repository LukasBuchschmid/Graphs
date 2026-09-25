import Graph.Hypergraphs

-- Graph 2G where we have 0 as V and 1 es ε
-- 0 edge : 0 → 1
-- 1 edge : 1 → 0
-- 2 edge : 1 → 1
def twoG : (Graph (Fin 3) (Fin 2)) where
  s
    | 0 => 0
    | 1 => 1
    | 2 => 1
  t
    | 0 => 1
    | 1 => 0
    | 2 => 1

structure PreOpenGraph (E : Type) (V : Type) where
  GraphStruct : Graph E V
  HomTwoG : GraphHom GraphStruct twoG

def isEdgeVertex {E V} (pog : PreOpenGraph E V) (v : V) : Prop :=
  pog.HomTwoG.mapV v = 1

def isRegularVertex {E V} (pog : PreOpenGraph E V) (v : V) : Prop :=
  pog.HomTwoG.mapV v = 0

def InEdges {E V} (g : Graph E V) (v : V) := {e : E // g.t e = v}

def OutEdges {E V} (g : Graph E V) (v : V) := {e : E // g.s e = v}

def InDegreeMostOne {E V} (g : Graph E V) (v : V) : Prop :=
  ∀ e₁ e₂ : (InEdges g v), e₁ = e₂

def OutDegreeMostOne {E V} (g : Graph E V) (v : V) : Prop :=
  ∀ e₁ e₂ : (OutEdges g v), e₁ = e₂

def isOpenGraph {E V} (g : PreOpenGraph E V) : Prop :=
  ∀ v : V , g.HomTwoG.mapV v = 1 → (OutDegreeMostOne g.GraphStruct v) ∧ (InDegreeMostOne g.GraphStruct v)

inductive Node (V EV : Type) where
  | vertex (v : V)
  | edgeVertex (ev : EV)

inductive OpenDAG (V EV : Type) : {nodes : List (Node V EV)} → DAG (Node V EV) nodes → Type
  | empty : OpenDAG V EV DAG.empty
  | addV  (v : V) {nodes : List (Node V EV)} {d : DAG (Node V EV) nodes} (prev : OpenDAG V EV d)
        (h_new : Node.vertex v ∉ nodes)
        (edges : List (Node V EV)) (h_edges : ∀ e ∈ edges, e ∈ nodes)
        (h_only_ev : ∀ e ∈ edges, ∃ ev, e = Node.edgeVertex ev)
        (h_nodup : edges.Nodup)
        (h_untargeted : ∀ e ∈ edges, ∀ old : DAGEdges d, DAGTarget d old ≠ e) :
        OpenDAG V EV (DAG.add (Node.vertex v) d h_new edges h_edges)
  | addEV (ev : EV) {nodes : List (Node V EV)} {d : DAG (Node V EV) nodes} (prev : OpenDAG V EV d)
        (h_new : Node.edgeVertex ev ∉ nodes)
        (edges : List (Node V EV)) (h_edges : ∀ e ∈ edges, e ∈ nodes)
        (h_size : edges.length ≤ 1)
        (h_untargeted : ∀ (ev : EV), Node.edgeVertex ev ∈ edges →
            ∀ old : DAGEdges d, DAGTarget d old ≠ Node.edgeVertex ev) :
        OpenDAG V EV (DAG.add (Node.edgeVertex ev) d h_new edges h_edges)

def OpenDAG.toDAG {V EV : Type} {nodes : List (Node V EV)} {d : DAG (Node V EV) nodes}
    (_ : OpenDAG V EV d) : DAG (Node V EV) nodes := d

def OpenDAGtwoGmapV {V EV : Type} {nodes : List (Node V EV)} {d : DAG (Node V EV) nodes}
  (_ : OpenDAG V EV d) : {v : (Node V EV) // v ∈ nodes} → Fin 2 :=
  fun v =>
    match v.val with
      | .vertex _ => 0
      | .edgeVertex _ => 1

def OpenDAGtwoGmapE {V EV : Type} {nodes : List (Node V EV)} {d : DAG (Node V EV) nodes}
  (od : OpenDAG V EV d) : (DAGEdges d) → Fin 3 :=
  match od with
  | .empty => fun e => nomatch e
  | .addV v prev h_new edges h_edges h_only_ev h_nodup h_untargeted => fun
    | .inl old_edge => OpenDAGtwoGmapE prev old_edge
    | .inr new_edge => 0
  | .addEV ev prev h_new edges h_edges h_size h_untargeted => fun
    | .inl old_edge => OpenDAGtwoGmapE prev old_edge
    | .inr new_edge =>
      match edges[new_edge] with
      | .vertex _ => 1
      | .edgeVertex _ => 2

theorem OpenDAGtwoGmapProp {V EV : Type} {nodes : List (Node V EV)} {d : DAG (Node V EV) nodes}
  (od : OpenDAG V EV d) : (e : DAGEdges d) →
    (twoG.s (OpenDAGtwoGmapE od e) = OpenDAGtwoGmapV od (d.toTightGraph.s e))
    ∧ (twoG.t (OpenDAGtwoGmapE od e) = OpenDAGtwoGmapV od (d.toTightGraph.t e)) :=
    match od with
    | .empty => by
      intro e
      trivial
    | .addV v prev h_new edges h_edges h_only_ev h_nodup h_untargeted => by
      intro e
      cases e with
        | inl old_edge => exact OpenDAGtwoGmapProp prev old_edge
        | inr new_edge =>
          obtain ⟨ev, h_eq⟩ := h_only_ev edges[new_edge] (List.getElem_mem new_edge.2)
          dsimp [OpenDAGtwoGmapE, OpenDAGtwoGmapV, DAG.toTightGraph, DAGSource, DAGTarget, twoG] at h_eq ⊢
          rw [h_eq]
          exact ⟨rfl, rfl⟩
    | .addEV ev prev h_new edges h_edges h_size h_untargeted => by
        intro e
        cases e with
          | inl old_edge => exact OpenDAGtwoGmapProp prev old_edge
          | inr new_edge =>
              match h : edges[new_edge] with
                | .vertex v =>
                  dsimp [DAG.toTightGraph, DAGSource, DAGTarget, OpenDAGtwoGmapV] at h ⊢
                  rw [h]
                  simp
                  dsimp [OpenDAGtwoGmapE] at h ⊢
                  rw [h]
                  simp
                  dsimp [twoG]
                  exact ⟨rfl, rfl⟩
                | .edgeVertex ev =>
                  dsimp [DAG.toTightGraph, DAGSource, DAGTarget, OpenDAGtwoGmapV] at h ⊢
                  rw [h]
                  simp
                  dsimp [OpenDAGtwoGmapE] at h ⊢
                  rw [h]
                  simp
                  dsimp [twoG]
                  exact ⟨rfl, rfl⟩

def OpenDAGtowG {V EV : Type} {nodes : List (Node V EV)} {d : DAG (Node V EV) nodes}
  (od : OpenDAG V EV d) : GraphHom d.toTightGraph twoG :=
  { mapE := OpenDAGtwoGmapE od
    mapV := OpenDAGtwoGmapV od
    sourceCompliant := fun e => (OpenDAGtwoGmapProp od e).1
    targetCompliant := fun e => (OpenDAGtwoGmapProp od e).2 }

def DAGtoPreOpenGraph {V EV : Type} {nodes : List (Node V EV)} {d : DAG (Node V EV) nodes}
  (od : OpenDAG V EV d) :
  PreOpenGraph (DAGEdges d) {v : (Node V EV) // v ∈ nodes} :=
  { GraphStruct := d.toTightGraph
    HomTwoG := OpenDAGtowG od }

theorem EdgeVertexOutDegree {V EV : Type} {nodes : List (Node V EV)} {d : DAG (Node V EV) nodes}
  (od : OpenDAG V EV d) (ev : EV)
  : (h_ev : Node.edgeVertex ev ∈ nodes) → OutDegreeMostOne d.toTightGraph ⟨(Node.edgeVertex ev), h_ev⟩ :=
    match od with
    | .empty => fun h_ev => nomatch h_ev
    | .addV v prev h_new edges h_edges h_only_ev h_nodup h_untargeted => by
      intro h_ev ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
      match e₁, e₂ with
        | .inl old₁, .inl old₂ =>
          apply Subtype.ext
          simp
          dsimp [DAG.toTightGraph, DAGSource] at h₁
          have h_old₁ := dag_source_mem prev.toDAG old₁
          have h_val₁ : DAGSource prev.toDAG old₁ = Node.edgeVertex ev := Subtype.ext_iff.mp h₁
          rw [h_val₁] at h_old₁
          dsimp [DAG.toTightGraph, DAGSource] at h₂
          have h_val₂ : DAGSource prev.toDAG old₂ = Node.edgeVertex ev := Subtype.ext_iff.mp h₂
          have h_out₁ : prev.toDAG.toTightGraph.s old₁ = ⟨Node.edgeVertex ev, h_old₁⟩ := Subtype.ext h_val₁
          have h_out₂ : prev.toDAG.toTightGraph.s old₂ = ⟨Node.edgeVertex ev, h_old₁⟩ := Subtype.ext h_val₂
          have h_eq := EdgeVertexOutDegree prev ev h_old₁ ⟨old₁, h_out₁⟩ ⟨old₂, h_out₂⟩
          have h_old_eq : old₁ = old₂ := Subtype.ext_iff.mp h_eq
          rw [h_old_eq]
        | .inr new₁, _ =>
          dsimp [DAG.toTightGraph, DAGSource] at h₁
          injection (Subtype.ext_iff.mp h₁)
        | .inl _, .inr new₂ =>
          dsimp [DAG.toTightGraph, DAGSource] at h₂
          injection (Subtype.ext_iff.mp h₂)
    | .addEV ev' prev h_new edges h_edges h_size h_untargeted => by
      intro h_ev ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
      match e₁, e₂ with
        | .inl old₁, .inl old₂ =>
          apply Subtype.ext
          simp
          dsimp [DAG.toTightGraph, DAGSource] at h₁
          have h_old₁ := dag_source_mem prev.toDAG old₁
          have h_val₁ : DAGSource prev.toDAG old₁ = Node.edgeVertex ev := Subtype.ext_iff.mp h₁
          rw [h_val₁] at h_old₁
          dsimp [DAG.toTightGraph, DAGSource] at h₂
          have h_val₂ : DAGSource prev.toDAG old₂ = Node.edgeVertex ev := Subtype.ext_iff.mp h₂
          have h_out₁ : prev.toDAG.toTightGraph.s old₁ = ⟨Node.edgeVertex ev, h_old₁⟩ := Subtype.ext h_val₁
          have h_out₂ : prev.toDAG.toTightGraph.s old₂ = ⟨Node.edgeVertex ev, h_old₁⟩ := Subtype.ext h_val₂
          have h_eq := EdgeVertexOutDegree prev ev h_old₁ ⟨old₁, h_out₁⟩ ⟨old₂, h_out₂⟩
          have h_old_eq : old₁ = old₂ := Subtype.ext_iff.mp h_eq
          rw [h_old_eq]
        | .inr new₁, .inr new₂ =>
          apply Subtype.ext
          simp
          have h_new_eq : new₁ = new₂ := by
            ext
            omega
          rw [h_new_eq]
        | .inr new₁, .inl old₂ =>
          dsimp [DAG.toTightGraph, DAGSource] at h₁ h₂
          have h_same : Node.edgeVertex ev' = Node.edgeVertex ev := Subtype.ext_iff.mp h₁
          have h_ev' : ev' = ev := by injection h_same
          have h_mem := dag_source_mem prev.toDAG old₂
          have h_src : DAGSource prev.toDAG old₂ = Node.edgeVertex ev := Subtype.ext_iff.mp h₂
          rw [h_src] at h_mem
          rw [h_ev'] at h_new
          contradiction
        | .inl old₁, .inr new₂ =>
          dsimp [DAG.toTightGraph, DAGSource] at h₁ h₂
          have h_same : Node.edgeVertex ev' = Node.edgeVertex ev := Subtype.ext_iff.mp h₂
          have h_ev' : ev' = ev := by injection h_same
          have h_mem := dag_source_mem prev.toDAG old₁
          have h_src : DAGSource prev.toDAG old₁ = Node.edgeVertex ev := Subtype.ext_iff.mp h₁
          rw [h_src] at h_mem
          rw [h_ev'] at h_new
          contradiction

theorem EdgeVertexInDegree {V EV : Type} {nodes : List (Node V EV)} {d : DAG (Node V EV) nodes}
  (od : OpenDAG V EV d) (ev : EV)
  : (h_ev : Node.edgeVertex ev ∈ nodes) → InDegreeMostOne d.toTightGraph ⟨(Node.edgeVertex ev), h_ev⟩ :=
    match od with
    | .empty => fun h_ev => nomatch h_ev
    | .addV v prev h_new edges h_edges h_only_ev h_nodup h_untargeted => by
      intro h_ev ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
      match e₁, e₂ with
        | .inl old₁, .inl old₂ =>
          apply Subtype.ext
          simp
          dsimp [DAG.toTightGraph, DAGTarget] at h₁
          have h_old₁ := dag_target_mem prev.toDAG old₁
          have h_val₁ : DAGTarget prev.toDAG old₁ = Node.edgeVertex ev := Subtype.ext_iff.mp h₁
          rw [h_val₁] at h_old₁
          dsimp [DAG.toTightGraph, DAGSource] at h₂
          have h_val₂ : DAGTarget prev.toDAG old₂ = Node.edgeVertex ev := Subtype.ext_iff.mp h₂
          have h_out₁ : prev.toDAG.toTightGraph.t old₁ = ⟨Node.edgeVertex ev, h_old₁⟩ := Subtype.ext h_val₁
          have h_out₂ : prev.toDAG.toTightGraph.t old₂ = ⟨Node.edgeVertex ev, h_old₁⟩ := Subtype.ext h_val₂
          have h_eq := EdgeVertexInDegree prev ev h_old₁ ⟨old₁, h_out₁⟩ ⟨old₂, h_out₂⟩
          have h_old_eq : old₁ = old₂ := Subtype.ext_iff.mp h_eq
          rw [h_old_eq]
        | .inr new₁, .inr new₂ =>
          apply Subtype.ext
          simp
          dsimp [DAG.toTightGraph, DAGTarget] at h₁ h₂
          have h₁_val : edges[↑new₁] = Node.edgeVertex ev := Subtype.ext_iff.mp h₁
          have h₂_val : edges[↑new₂] = Node.edgeVertex ev := Subtype.ext_iff.mp h₂
          have h_target_eq : edges[↑new₁] = edges[↑new₂] := h₁_val.trans h₂_val.symm
          have h_idx_eq : (new₁ : Nat) = (new₂ : Nat) := List.Nodup.getElem_inj h_nodup |>.mp h_target_eq
          have h_fin_eq : new₁ = new₂ := Fin.ext h_idx_eq
          rw [h_fin_eq]
        | .inr new₁, .inl old₂ =>
          dsimp [DAG.toTightGraph, DAGTarget] at h₁ h₂
          have h_mem := dag_target_mem prev.toDAG old₂
          expose_names
          have h₁_val := Subtype.ext_iff.mp h₁
          have h₂_val := Subtype.ext_iff.mp h₂
          have h_target_eq : edges[new₁] = DAGTarget d_1 old₂ := h₁_val.trans h₂_val.symm
          have helper : (edges[new₁] ∈ edges) := by simp
          have h_unt := h_untargeted edges[new₁] helper old₂
          have := h_target_eq.symm
          contradiction
        | .inl old₁, .inr new₂ =>
          dsimp [DAG.toTightGraph, DAGTarget] at h₁ h₂
          have h_mem := dag_target_mem prev.toDAG old₁
          expose_names
          have h₁_val := Subtype.ext_iff.mp h₁
          have h₂_val := Subtype.ext_iff.mp h₂
          have h_target_eq : DAGTarget d_1 old₁ = edges[new₂] := h₁_val.trans h₂_val.symm
          have helper : (edges[new₂] ∈ edges) := by simp
          have h_unt := h_untargeted edges[new₂] helper old₁
          have := h_target_eq.symm
          contradiction
    | .addEV ev' prev h_new edges h_edges h_size h_untargeted => by
      intro h_ev ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
      match e₁, e₂ with
        | .inl old₁, .inl old₂ =>
          apply Subtype.ext
          simp
          dsimp [DAG.toTightGraph, DAGTarget] at h₁
          have h_old₁ := dag_target_mem prev.toDAG old₁
          have h_val₁ : DAGTarget prev.toDAG old₁ = Node.edgeVertex ev := Subtype.ext_iff.mp h₁
          rw [h_val₁] at h_old₁
          dsimp [DAG.toTightGraph, DAGSource] at h₂
          have h_val₂ : DAGTarget prev.toDAG old₂ = Node.edgeVertex ev := Subtype.ext_iff.mp h₂
          have h_out₁ : prev.toDAG.toTightGraph.t old₁ = ⟨Node.edgeVertex ev, h_old₁⟩ := Subtype.ext h_val₁
          have h_out₂ : prev.toDAG.toTightGraph.t old₂ = ⟨Node.edgeVertex ev, h_old₁⟩ := Subtype.ext h_val₂
          have h_eq := EdgeVertexInDegree prev ev h_old₁ ⟨old₁, h_out₁⟩ ⟨old₂, h_out₂⟩
          have h_old_eq : old₁ = old₂ := Subtype.ext_iff.mp h_eq
          rw [h_old_eq]
        | .inr new₁, .inr new₂ =>
          apply Subtype.ext
          simp
          have h_new_eq : new₁ = new₂ := by
            ext
            omega
          rw [h_new_eq]
        | .inr new₁, .inl old₂ =>
          dsimp [DAG.toTightGraph, DAGTarget] at h₁ h₂
          have h_same : edges[new₁] = Node.edgeVertex ev := Subtype.ext_iff.mp h₁
          have h_mem := dag_target_mem prev.toDAG old₂
          have h_src : DAGTarget prev.toDAG old₂ = Node.edgeVertex ev := Subtype.ext_iff.mp h₂
          rw [h_src] at h_mem
          expose_names
          have helper : edges[new₁] ∈ edges := by simp
          rw[h_same] at helper
          have h_cont := h_untargeted ev helper old₂
          contradiction
        | .inl old₁, .inr new₂ =>
          dsimp [DAG.toTightGraph, DAGTarget] at h₁ h₂
          have h_same : edges[new₂] = Node.edgeVertex ev := Subtype.ext_iff.mp h₂
          have h_mem := dag_target_mem prev.toDAG old₁
          have h_src : DAGTarget prev.toDAG old₁ = Node.edgeVertex ev := Subtype.ext_iff.mp h₁
          rw [h_src] at h_mem
          expose_names
          have helper : edges[new₂] ∈ edges := by simp
          rw[h_same] at helper
          have h_cont := h_untargeted ev helper old₁
          contradiction

theorem OpenDAGisOpenGraph {V EV : Type} {nodes : List (Node V EV)} {d : DAG (Node V EV) nodes}
  (od : OpenDAG V EV d) : isOpenGraph (DAGtoPreOpenGraph od) := by
    dsimp [isOpenGraph, twoG, DAGtoPreOpenGraph, OpenDAGtowG]
    intro ⟨ev, h⟩ h_ev
    cases ev with
      | vertex v =>
        dsimp [OpenDAGtwoGmapV] at h_ev
        contradiction
      | edgeVertex ev' =>
        exact ⟨(EdgeVertexOutDegree od ev' h), (EdgeVertexInDegree od ev' h)⟩
