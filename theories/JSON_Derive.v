From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From rocq_json_derivers Extra Dependency "jsonifiable.elpi" as jsonifiable.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.

From elpi Require Import elpi.
From elpi Require Import derive.
From elpi Require Import derive.std.

From RocqJSON Require Import JSON JSON_Error_Strings.
From Stdlib Require Import Lia.
From Stdlib Require Import Wf_nat.

Local Open Scope string_scope.

(* ===== Database ===== *)
Elpi Db derive.jsonifiable.db lp:{{
  pred jsonifiable-done o:gref.
}}.

(* ===== Ltac1 tactics for Elpi to call ===== *)

(* Solves JSON_depth sub < JSON_depth js obligations *)
Ltac solve_json_depth := simpl; lia.

(* Helper: solve the Fix_eq extensionality side-condition *)
Ltac fix_eq_ext :=
  intros;
  repeat match goal with
  | |- context [match ?x with _ => _ end] => destruct x
  end;
  reflexivity.

(* Main canonical roundtrip proof tactic.
   Uses induction to handle recursive types via IH.
   - simpl unfolds to_json/from_json on concrete constructors
   - IH rewrites recursive calls: from_json(to_json t) = res t
   - canonical_jsonification rewrites from_JSON(to_JSON x) = res x
   - string_dec on equal strings reduces to left refl *)
Ltac derive_jsonifiable_proof :=
  let v := fresh "v" in
  intro v; induction v; simpl;
  repeat match goal with
  | IH : ?from_json (?to_json _) = _ |- _ => rewrite IH
  end;
  repeat rewrite canonical_jsonification; simpl;
  try reflexivity.

(* ===== Step 1: Minimal test - just explore the Elpi environment ===== *)

(* First, let's just load the file and see if it compiles *)
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

(* ===== Step 2: Debug query - inspect the inductive ===== *)

(* Simple enum type to test with *)
Inductive color := Red | Green | Blue.
derive color.

Elpi Query lp:{{
  coq.locate "color" (indt Ind),
  coq.env.indt Ind _IsInd ParNo UParNo _IndSort Kns KTs,
  coq.say "color has" ParNo "params," UParNo "uniform params",
  coq.say "constructors:" Kns,
  coq.say "constructor types:" KTs,
  (if (coq.env.recursive? Ind) (coq.say "is recursive: yes") (coq.say "is recursive: no"))
}}.



(* ===== Test 1: Simple enum ===== *)
Elpi derive.jsonifiable color.
Check color_Jsonifiable.
Compute (to_JSON Green : JSON).
Print from_JSON.
Compute (from_JSON (to_JSON Red) : Result color string).

(* ===== Test 2: Constructors with non-recursive arguments (nat is Jsonifiable) ===== *)
Inductive foo := Fa (n : nat) | Fb (m1 m2 : nat).
derive foo.
Elpi derive.jsonifiable foo.
Check foo_Jsonifiable.
Compute (to_JSON (Fa 42) : JSON).
Compute (from_JSON (to_JSON (Fb 7 13)) : Result foo string).

(* ===== Test 3: Recursive type ===== *)
Inductive tree := Leaf | Node (l : tree) (n : nat) (r : tree).

derive tree.
Elpi derive.jsonifiable tree.
Check tree_Jsonifiable.
Compute (to_JSON (Node Leaf 42 Leaf) : JSON).
Compute (from_JSON (to_JSON (Node Leaf 42 Leaf)) : Result tree string).
Compute (from_JSON (to_JSON (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf))) : Result tree string).
