From elpi Require Import elpi.
From elpi Require Import derive.
From elpi Require Import derive.std.

From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From rocq_json_derivers Extra Dependency "jsonifiable.elpi" as jsonifiable.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.


From RocqJSON Require Import JSON JSON_Error_Strings.
From Stdlib Require Import Lia.
From Stdlib Require Import Wf_nat.

Local Open Scope string_scope.

(* ===== Database ===== *)
Elpi Db derive.jsonifiable.db lp:{{
  pred jsonifiable-done o:gref.
}}.

(* NOTE: This is called by "jsonifiable.elpi" to solve the main goal of deriving JSON_Derive.Jsonifiable for a given inductive type. 

  Main canonical roundtrip proof tactic.
   Uses induction to handle recursive types via IH.
   - simpl unfolds to_json/from_json on concrete constructors
   - IH rewrites recursive calls: from_json(to_json t) = res t
   - canonical_jsonification rewrites from_JSON(to_JSON x) = res x
   - string_dec on equal strings reduces to left refl *)
Ltac derive_jsonifiable_proof :=
  (* intro all forall-bound variables (type params, TC instances, the inductive value) *)
  intros;
  match goal with
  | v : _ |- _ => induction v
  end; simpl;
  repeat (match goal with
  | IH : ?from_json (?to_json _) = _ |- _ => rewrite IH
  end);
  repeat rewrite canonical_jsonification; simpl;
  try reflexivity.

Elpi Command derive.jsonifiable.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db derive.jsonifiable.db.
Elpi Accumulate File jsonifiable.
Elpi Accumulate lp:{{
  main [str I] :- !,
    coq.locate I GR,
    coq.gref->id GR Tname,
    Prefix is Tname ^ "_",
    derive.jsonifiable.main GR Prefix _.
  main _ :- coq.error "Usage: derive.jsonifiable <object name>".
}}.

Elpi Accumulate derive Db derive.jsonifiable.db.
Elpi Accumulate derive File jsonifiable.
Elpi Accumulate derive lp:{{
  derivation GR Pref ff (derive "jsonifiable" (derive.jsonifiable.main GR Pref) (jsonifiable-done GR)).
}}.

(* Simple enum type to test with *)
Inductive color := Red | Green | Blue.
derive color.
Check color_Jsonifiable.
Compute (to_JSON Green : JSON).
Compute (from_JSON (to_JSON Red) : Result color string).

(* Constructors with non-recursive arguments (nat is Jsonifiable) ===== *)
Inductive foo := Fa (n : nat) | Fb (m1 m2 : nat).
derive foo.
Check foo_Jsonifiable.
Compute (to_JSON (Fa 42) : JSON).
Compute (from_JSON (to_JSON (Fb 7 13)) : Result foo string).

(* ===== Test 3: Recursive type ===== *)
Inductive tree := Leaf | Node (l : tree) (n : nat) (r : tree).
derive tree.
Check tree_Jsonifiable.
Compute (to_JSON (Node Leaf 42 Leaf) : JSON).
Compute (from_JSON (to_JSON (Node Leaf 42 Leaf)) : Result tree string).
Compute (from_JSON (to_JSON (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf))) : Result tree string).

(* ===== Test 4: Parametric recursive type ===== *)
Inductive jtree (A : Type) :=
  | JLeaf : jtree
  | JNode : A -> jtree -> jtree -> jtree.
Arguments JLeaf {A}.
Arguments JNode {A} _ _ _.
derive jtree.

(* Manual roundtrip test to verify the derivation worked *)
Check jtree_Jsonifiable.
(* Set Typeclasses Debug.
Set Typeclasses Depth 10. *)
Compute (to_JSON (JNode 42 JLeaf JLeaf) : JSON).
Compute (from_JSON (to_JSON (JNode 42 JLeaf JLeaf)) : Result (jtree nat) string).

Unset Uniform Inductive Parameters.

(* ===== Test 5: More complex parametric recursive type ===== *)
Inductive ab_tree (A B : Type) :=
  | ABLeaf : ab_tree A B
  | ABNode (a : A) (tree' : ab_tree A B) (b : B) : ab_tree A B.
Arguments ABLeaf {A B}.
Arguments ABNode {A B} _ _ _.

derive ab_tree.
Check ab_tree_Jsonifiable.
Compute (to_JSON (ABNode 1 ABLeaf true) : JSON).
Compute (from_JSON (to_JSON (ABNode 1 ABLeaf true)) : Result (ab_tree nat bool) string).