import Graph.Hypergraphs

-- ============================================================
-- Section: Bridge E-Hypergraphs with Extended Interfaces
-- ============================================================

/-- The edge kinds in a Bridge E-Hypergraph.
    Bridges now explicitly represent the f_int and g_int interface mappings. -/
inductive EdgeKind (E ChoiceID Sign : Type _)
  | base (s : Sign)
  | ebox
  | bridgeIn  (box : E) (choice : ChoiceID)
  | bridgeOut (box : E) (choice : ChoiceID)
  deriving DecidableEq

/-- The purely computational data of a Bridge Graph.
    This is what pattern matching and extraction algorithms actually run on.
    Notice there are zero proofs required to instantiate this! -/
structure BridgeGraph (E V ChoiceID Sign : Type _) where
  hg : Hypergraph E V
  kind : E → EdgeKind E ChoiceID Sign
  /-- Acts as the canonical "Union-Find" root to identify a specific Choice. -/
  choice_anchor : E → ChoiceID → (V ⊕ E)
  /-- Direct mapping from an E-box and choice to its input bridge edge -/
  bridge_in  : (box : E) → kind box = .ebox → ChoiceID → E
  /-- Direct mapping from an E-box and choice to its output bridge edge -/
  bridge_out : (box : E) → kind box = .ebox → ChoiceID → E

/-- The mathematical laws that guarantee a BridgeGraph represents a valid E-Hypergraph.
    Algorithms don't need to compute these, but theorems will assume them via `[BridgeGraphLaws G]`. -/
class BridgeGraphLaws {E V ChoiceID Sign : Type _} (G : BridgeGraph E V ChoiceID Sign) where

  -- The mathematical hierarchy and consistency relations
  child : (V ⊕ E) → (V ⊕ E) → Prop
  child_strict : StrictPartialOrder child

  consistency : (p : V ⊕ E) → ChildOf child p → ChildOf child p → Prop
  consistency_equiv : ∀ (p : V ⊕ E), Equivalence (consistency p)

  -- ============================================================
  -- 1) Standard Hierarchy Axioms
  -- ============================================================
  parents_are_eboxes : ∀ (a p : V ⊕ E), child p a →
    ∃ e : E, p = .inr e ∧ G.kind e = .ebox

  at_most_one_immediate_parent : ∀ (x p₁ p₂ : V ⊕ E),
    ImmParent child p₁ x → ImmParent child p₂ x → p₁ = p₂

  maximal_edges_not_ebox : ∀ (e : E),
    (∀ x' : V ⊕ E, ¬ child (.inr e) x') → G.kind e ≠ .ebox

  -- ============================================================
  -- 2) Scope Preservation (exempting bridges)
  -- ============================================================
  scope_preserve_source : ∀ (e : E) (v : V) (p : V ⊕ E),
    (∀ b c, G.kind e ≠ .bridgeIn b c) → (∀ b c, G.kind e ≠ .bridgeOut b c) →
    v ∈ G.hg.s e → (ImmParent child p (.inr e) ↔ ImmParent child p (.inl v))

  scope_preserve_target : ∀ (e : E) (v : V) (p : V ⊕ E),
    (∀ b c, G.kind e ≠ .bridgeIn b c) → (∀ b c, G.kind e ≠ .bridgeOut b c) →
    v ∈ G.hg.t e → (ImmParent child p (.inr e) ↔ ImmParent child p (.inl v))

  -- ============================================================
  -- 3) Anchor Validity
  -- ============================================================
  anchor_is_child : ∀ (b box : E) (c : ChoiceID),
    (G.kind b = .bridgeIn box c ∨ G.kind b = .bridgeOut box c) →
    ImmParent child (.inr box) (G.choice_anchor box c)

  -- ============================================================
  -- 4) Interface Alignment (Reifying f_int and g_int)
  -- ============================================================
  bridge_in_alignment : ∀ (b box : E) (c : ChoiceID),
    G.kind b = .bridgeIn box c →
    G.kind box = .ebox ∧
    (G.hg.s b = G.hg.s box) ∧
    ((G.hg.t b).length = (G.hg.s box).length) ∧
    (G.hg.t b).Nodup ∧
    (∀ v ∈ G.hg.t b, ImmParent child (.inr box) (.inl v)) ∧
    (∀ (e : E) (he : ImmParent child (.inr box) (.inr e))
       (h_anchor : ImmParent child (.inr box) (G.choice_anchor box c)),
       consistency (.inr box) ⟨.inr e, he⟩ ⟨G.choice_anchor box c, h_anchor⟩ →
       ∀ v ∈ G.hg.t b, v ∉ G.hg.t e)

  bridge_out_alignment : ∀ (b box : E) (c : ChoiceID),
    G.kind b = .bridgeOut box c →
    G.kind box = .ebox ∧
    (G.hg.t b = G.hg.t box) ∧
    ((G.hg.s b).length = (G.hg.t box).length) ∧
    (G.hg.s b).Nodup ∧
    (∀ v ∈ G.hg.s b, ImmParent child (.inr box) (.inl v)) ∧
    (∀ (e : E) (he : ImmParent child (.inr box) (.inr e))
       (h_anchor : ImmParent child (.inr box) (G.choice_anchor box c)),
       consistency (.inr box) ⟨.inr e, he⟩ ⟨G.choice_anchor box c, h_anchor⟩ →
       ∀ v ∈ G.hg.s b, v ∉ G.hg.s e)

  -- ============================================================
  -- 5) Choice Consistency (Bridges connect to their anchored choice)
  -- ============================================================

  bridge_in_consistency : ∀ (b box : E) (c : ChoiceID),
    G.kind b = .bridgeIn box c →
    ∀ v ∈ G.hg.t b,
    ∀ (h_child_v : ImmParent child (.inr box) (.inl v))
      (h_child_anchor : ImmParent child (.inr box) (G.choice_anchor box c)),
      consistency (.inr box) ⟨.inl v, h_child_v⟩ ⟨G.choice_anchor box c, h_child_anchor⟩

  bridge_out_consistency : ∀ (b box : E) (c : ChoiceID),
    G.kind b = .bridgeOut box c →
    ∀ v ∈ G.hg.s b,
    ∀ (h_child_v : ImmParent child (.inr box) (.inl v))
      (h_child_anchor : ImmParent child (.inr box) (G.choice_anchor box c)),
      consistency (.inr box) ⟨.inl v, h_child_v⟩ ⟨G.choice_anchor box c, h_child_anchor⟩

  -- consistency is closed under connectivity (excluding bridges)
  consistency_closed_connectivity : ∀ (p : V ⊕ E) (e : E) (v : V)
    (hp_e : ImmParent child p (.inr e))
    (hp_v : ImmParent child p (.inl v)),
    (∀ b c, G.kind e ≠ .bridgeIn b c) → (∀ b c, G.kind e ≠ .bridgeOut b c) →
    (v ∈ G.hg.s e ∨ v ∈ G.hg.t e) →
    consistency p ⟨.inl v, hp_v⟩ ⟨.inr e, hp_e⟩

  consistency_nontrivial : ∀ (p : V ⊕ E),
    (∃ x, ImmParent child p x) →
    ∃ (x y : ChildOf child p), ¬ consistency p x y

  -- ============================================================
  -- 6) Exhaustiveness (Every choice has a bridge)
  -- ============================================================
  bridge_in_exhaustive : ∀ (box : E) (x : V ⊕ E) (hx : ImmParent child (.inr box) x),
    G.kind box = .ebox →
    ∃ (b : E) (c : ChoiceID),
      G.kind b = .bridgeIn box c ∧
      ∃ (h_child_anchor : ImmParent child (.inr box) (G.choice_anchor box c)),
        consistency (.inr box) ⟨x, hx⟩ ⟨G.choice_anchor box c, h_child_anchor⟩

  bridge_out_exhaustive : ∀ (box : E) (x : V ⊕ E) (hx : ImmParent child (.inr box) x),
    G.kind box = .ebox →
    ∃ (b : E) (c : ChoiceID),
      G.kind b = .bridgeOut box c ∧
      ∃ (h_child_anchor : ImmParent child (.inr box) (G.choice_anchor box c)),
        consistency (.inr box) ⟨x, hx⟩ ⟨G.choice_anchor box c, h_child_anchor⟩

  -- ============================================================
  -- 7) Uniqueness / Injectivity (No redundant bridges)
  -- ============================================================
  bridge_in_at_most_one : ∀ (b1 b2 box : E) (c : ChoiceID),
    G.kind b1 = .bridgeIn box c → G.kind b2 = .bridgeIn box c → b1 = b2

  bridge_out_at_most_one : ∀ (b1 b2 box : E) (c : ChoiceID),
    G.kind b1 = .bridgeOut box c → G.kind b2 = .bridgeOut box c → b1 = b2

  choice_anchor_unique : ∀ (b1 b2 box : E) (c1 c2 : ChoiceID),
    G.kind b1 = .bridgeIn box c1 →
    G.kind b2 = .bridgeIn box c2 →
    ∀ (hc1 : ImmParent child (.inr box) (G.choice_anchor box c1))
      (hc2 : ImmParent child (.inr box) (G.choice_anchor box c2)),
      c1 ≠ c2 →
      ¬ consistency (.inr box) ⟨G.choice_anchor box c1, hc1⟩ ⟨G.choice_anchor box c2, hc2⟩

  -- ============================================================
  -- 8) Bridge Pairing (Every choice has an entrance and an exit to the same E-box)
  -- ============================================================
  bridge_pair_in_out : ∀ (b_in box : E) (c : ChoiceID),
    G.kind b_in = .bridgeIn box c →
    ∃ b_out : E, G.kind b_out = .bridgeOut box c

  bridge_pair_out_in : ∀ (b_out box : E) (c : ChoiceID),
    G.kind b_out = .bridgeOut box c →
    ∃ b_in : E, G.kind b_in = .bridgeIn box c

  -- ============================================================
  -- 9) Direct Bridge Function Invariants
  -- ============================================================
  bridge_in_correct : ∀ (box : E) (h : G.kind box = .ebox) (c : ChoiceID),
    G.kind (G.bridge_in box h c) = .bridgeIn box c

  bridge_out_correct : ∀ (box : E) (h : G.kind box = .ebox) (c : ChoiceID),
    G.kind (G.bridge_out box h c) = .bridgeOut box c


def FlattenBridgeGraphEdges  (bg : BridgeGraph E V ChoiceID Sign) : Type _ :=
  { e : E // bg.kind e = EdgeKind.ebox ∨ ∃ s : Sign , bg.kind e = EdgeKind.base s}

def RemoveBridgeEdgeSource [DecidableEq V] (bg : BridgeGraph E V ChoiceID Sign) (box : E) (h_box : bg.kind box = EdgeKind.ebox) (choice : ChoiceID) :
  E → List V :=
    let e_out := bg.bridge_out box h_box choice
    fun e =>
      if bg.hg.s e = bg.hg.t box then
        bg.hg.s e_out
      else if bg.hg.s e = bg.hg.s box then
        bg.hg.t e
      else
        bg.hg.s e

def RemoveBridgeEdgeTarget [DecidableEq V] (bg : BridgeGraph E V ChoiceID Sign) (box : E) (h_box : bg.kind box = EdgeKind.ebox) (choice : ChoiceID) :
  E → List V :=
    let e_in := bg.bridge_in box h_box choice
    fun e =>
      if bg.hg.t e = bg.hg.s box then
        bg.hg.t e_in
      else if bg.hg.t e = bg.hg.t box then
        bg.hg.s e
      else
        bg.hg.t e


def RemoveBridgeEdgeHG [DecidableEq V] (bg : BridgeGraph E V ChoiceID Sign) (box : E) (h_box : bg.kind box = EdgeKind.ebox) (choice : ChoiceID) :
  Hypergraph E V :=
    { s := RemoveBridgeEdgeSource bg box h_box choice
      t := RemoveBridgeEdgeTarget bg box h_box choice }

def RemoveBridgeEdge [DecidableEq V] (bg : BridgeGraph E V ChoiceID Sign) (box : E) (h_box : bg.kind box = EdgeKind.ebox) (choice : ChoiceID) :
  BridgeGraph E V ChoiceID Sign :=
  { hg := RemoveBridgeEdgeHG bg box h_box choice
    kind := bg.kind
    choice_anchor := bg.choice_anchor
    bridge_in := bg.bridge_in
    bridge_out := bg.bridge_out }


/-- A choice context records which choice branch is activated for an E-box. -/
abbrev ChoiceContext (E ChoiceID : Type _) := List (E × ChoiceID)

/-- Bridge reachability relation (⤳_C) through active bridges. -/
inductive BridgeReachability {E V ChoiceID Sign : Type _}
    (bg : BridgeGraph E V ChoiceID Sign) (C : ChoiceContext E ChoiceID) : V → V → Prop where
  | refl (v : V) : BridgeReachability bg C v v
  | bridgeIn (b box : E) (c : ChoiceID) (u v : V)
      (hk : bg.kind b = .bridgeIn box c)
      (hc : (box, c) ∈ C)
      (hp : (u, v) ∈ (bg.hg.s b).zip (bg.hg.t b)) :
      BridgeReachability bg C u v
  | bridgeOut (b box : E) (c : ChoiceID) (u v : V)
      (hk : bg.kind b = .bridgeOut box c)
      (hc : (box, c) ∈ C)
      (hp : (u, v) ∈ (bg.hg.s b).zip (bg.hg.t b)) :
      BridgeReachability bg C u v
  | trans {u v w : V} :
      BridgeReachability bg C u v → BridgeReachability bg C v w → BridgeReachability bg C u w

/-- Pointwise reachability between port sequences. -/
inductive PortsReach {V : Type _} (R : V → V → Prop) : List V → List V → Prop where
  | nil : PortsReach R [] []
  | cons {u v : V} {us vs : List V} (h : R u v) (hs : PortsReach R us vs) :
      PortsReach R (u :: us) (v :: vs)

/-- Map edge kinds across different edge types. -/
def EdgeKind.map {E₁ E₂ ChoiceID Sign : Type _} (f : E₁ → E₂) (k : EdgeKind E₁ ChoiceID Sign) :
    EdgeKind E₂ ChoiceID Sign :=
  match k with
  | .base s => .base s
  | .ebox => .ebox
  | .bridgeIn b c => .bridgeIn (f b) c
  | .bridgeOut b c => .bridgeOut (f b) c

/-- A Bridge Morphism between bridge graphs modulo reachability in the host graph. -/
structure BridgeMorphism {E₁ V₁ E₂ V₂ ChoiceID Sign : Type _}
    (bg₁ : BridgeGraph E₁ V₁ ChoiceID Sign) (bg₂ : BridgeGraph E₂ V₂ ChoiceID Sign) where
  mapE : E₁ → E₂
  mapV : V₁ → V₂
  choice_context : ChoiceContext E₂ ChoiceID
  consistent : ∀ {b : E₂} {c1 c2 : ChoiceID},
    (b, c1) ∈ choice_context → (b, c2) ∈ choice_context → c1 = c2
  kind_preserving (e : E₁) : bg₂.kind (mapE e) = EdgeKind.map mapE (bg₁.kind e)
  source_reach (e : E₁) : PortsReach (BridgeReachability bg₂ choice_context)
    ((bg₁.hg.s e).map mapV) (bg₂.hg.s (mapE e))
  target_reach (e : E₁) : PortsReach (BridgeReachability bg₂ choice_context)
    (bg₂.hg.t (mapE e)) ((bg₁.hg.t e).map mapV)
