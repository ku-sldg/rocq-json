From elpi Require Import elpi.
From elpi Require Import derive.
From elpi Require Import derive.std.

From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From rocq_json_derivers Extra Dependency "jsonifiable.elpi" as jsonifiable.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.


From RocqJSON Require Import JSON JSON_Error_Strings.
From Stdlib Require Import Lia.
From Stdlib Require Import List.

Local Open Scope string_scope.

(* Set Typeclasses Debug. *)
Set Typeclasses Depth 3.

(* ===== Database ===== *)
Elpi Db derive.jsonifiable.db lp:{{
  pred jsonifiable-done o:gref.
}}.

(* NOTE: This is called by "jsonifiable.elpi" to solve the main goal of deriving
   JSON_Derive.Jsonifiable for a given inductive type. *)

(* prove_result_map_eq: prove result_map g (map f l) = res l for arbitrarily
   nested element types. Uses IH_rec from outer fix (if in scope) and
   canonical_jsonification for abstract TC args. Handles arbitrary nesting
   depth by recursive invocation for inner result_map patterns.
   The induction pattern [| [? ?] ? IHl] assumes list elements are pairs. *)
Ltac prove_result_map_eq :=
  match goal with
  | |- result_map ?g (map ?f ?l) = res ?l =>
      induction l as [| [? ?] ? IHl]; simpl;
      [ try reflexivity
      | repeat (first [
          match goal with | IH : forall _, _ = res _ |- _ => rewrite IH end |
          rewrite canonical_jsonification |
          rewrite IHl
        ]);
        simpl;
        repeat (
          match goal with
          | |- context [result_map ?g2 (map ?f2 ?l2)] =>
              let Hmap := fresh "Hmap" in
              assert (Hmap : result_map g2 (map f2 l2) = res l2) by
                prove_result_map_eq;
              rewrite Hmap; simpl
          end
        );
        try reflexivity ]
  end.

(* For non-recursive types: no fix needed, just destruct *)
Ltac derive_jsonifiable_proof_norec :=
  intros;
  match goal with
  | v : _ |- _ =>
      revert v; intro v; destruct v
  end;
  simpl;
  repeat (rewrite canonical_jsonification);
  simpl;
  try reflexivity.

(* For recursive / nested-recursive types: fix gives universally quantified IH.
   For the nested case (self-type inside list containers), we assert the
   result_map lemma and prove it using prove_result_map_eq, which handles
   arbitrary nesting depth recursively. The key is that nt (from destructuring
   a cons element inside list_rect) is a structural subterm of the fix arg,
   so IH_rec nt passes the guard checker. *)
Ltac derive_jsonifiable_proof :=
  intros;
  match goal with
  | v : _ |- _ =>
      (* it is safe to do it this way since we control the context 
        and know the *last* introduced will always be the one we want *)
      revert v;
      fix IH_rec 1;
      intro v; destruct v
  end;
  simpl;
  repeat (first [
    match goal with | IH : forall _, _ = res _ |- _ => rewrite IH end |
    rewrite canonical_jsonification
  ]);
  simpl;
  try reflexivity;
  repeat (
    match goal with
    | |- context [result_map ?g (map ?f ?l)] =>
        let Hmap := fresh "Hmap" in
        assert (Hmap : result_map g (map f l) = res l) by prove_result_map_eq;
        rewrite Hmap; simpl
    end
  );
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
Elpi derive.jsonifiable color.
Check color_Jsonifiable.
Definition test_color := Green.
Compute (to_JSON test_color : JSON).
Compute (from_JSON (to_JSON test_color) : Result color string).
Print color_canonical_jsonification.

(* Constructors with non-recursive arguments (nat is Jsonifiable) ===== *)
Inductive foo := Fa (n : nat) | Fb (m1 m2 : nat).
Elpi derive.jsonifiable foo.
Check foo_Jsonifiable.
Definition test_foo := Fb 7 13.
Compute (to_JSON test_foo : JSON).
Compute (from_JSON (to_JSON test_foo) : Result foo string).

(* ===== Test 3: Recursive type ===== *)
Inductive tree := Leaf | Node (l : tree) (n : nat) (r : tree).
Elpi derive.jsonifiable tree.
Check tree_Jsonifiable.
Definition test_tree := Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf).
Compute (to_JSON test_tree : JSON).
Compute (from_JSON (to_JSON test_tree) : Result tree string).

(* ===== Test 4: Parametric recursive type ===== *)
Inductive jtree (A : Type) :=
  | JLeaf : jtree
  | JNode : A -> jtree -> jtree -> jtree.
Arguments JLeaf {A}.
Arguments JNode {A} _ _ _.
Elpi derive.jsonifiable jtree.
Check jtree_Jsonifiable.
Definition test_jtree := JNode 42 JLeaf JLeaf.
Compute (to_JSON test_jtree : JSON).
Compute (from_JSON (to_JSON test_jtree) : Result (jtree nat) string).

(* Testing with Uniform Inductive Parameters disabled as well *)
Unset Uniform Inductive Parameters.

(* ===== Test 5: More complex parametric recursive type ===== *)
Inductive ab_tree (A B : Type) :=
  | ABLeaf : ab_tree A B
  | ABNode (a : A) (tree' : ab_tree A B) (b : B) : ab_tree A B.
Arguments ABLeaf {A B}.
Arguments ABNode {A B} _ _ _.
Elpi derive.jsonifiable ab_tree.
Check ab_tree_Jsonifiable.
Definition test_ab_tree := ABNode 1 ABLeaf true.
Compute (to_JSON test_ab_tree : JSON).
Compute (from_JSON (to_JSON test_ab_tree) : Result (ab_tree nat bool) string).

(* ===== Test 6: Record type ===== *)
Record test_rec := {
  a : nat;
  b : bool;
  c : tree
}.
Elpi derive.jsonifiable test_rec.
Check test_rec_Jsonifiable.
Definition test_test_rec := {| a := 42; b := true; c := Node Leaf 1 Leaf |}.
Compute (to_JSON test_test_rec : JSON).
Compute (from_JSON (to_JSON test_test_rec) : Result test_rec string).

(* ===== Test 7: Polymorphic Record type ===== *)
Record prec (A B : Type) := {
  pa : A;
  pb : B;
  pc : ab_tree A B
}.
Elpi derive.jsonifiable prec.
Check prec_Jsonifiable.
Definition test_prec :=
  {| pa := 42; pb := true; pc := (ABNode 0 ABLeaf false) |}.
Compute (to_JSON test_prec : JSON).
Compute (from_JSON (to_JSON test_prec) : Result (prec nat bool) string).

(* ==== Test 8: Integers ===== *)
Elpi derive.jsonifiable positive.
Elpi derive.jsonifiable Z.

(* ===== Test 9: Nested recursive type ===== *)
Inductive nested_tree (A : Type) :=
  | NLeaf : nested_tree A
  | NNode : list (A * nested_tree A) -> nested_tree A.
Arguments NLeaf {A}.
Arguments NNode {A} _.
Elpi derive.jsonifiable nested_tree.

Definition test_nested_tree := NNode [(42, NLeaf); (7, NNode [(13, NLeaf)])].
Compute (to_JSON test_nested_tree : JSON).
Compute (from_JSON (to_JSON test_nested_tree) : Result (nested_tree nat) string).

(* ===== Test 10: Complex Nested Type ===== *)
Inductive nested_tree_2 (A B : Type) :=
  | NLeaf2 : nested_tree_2 A B
  | NNode2 : list (A * nested_tree_2 A B) -> list (B * nested_tree_2 A B) -> nested_tree_2 A B.
Arguments NLeaf2 {A B}.
Arguments NNode2 {A B} _ _.
Elpi derive.jsonifiable nested_tree_2.

Definition test_nested_tree_2 := NNode2 [(42, NLeaf2); (7, NNode2 [(13, NLeaf2)] [])] [(true, NLeaf2); (false, NNode2 [] [(true, NLeaf2)])].
Compute (to_JSON test_nested_tree_2 : JSON).
Compute (from_JSON (to_JSON test_nested_tree_2) : Result (nested_tree_2 nat bool) string).

(* ===== Test 11: A many constructor type ===== *)
Inductive many_constructors :=
  | MC0
  | MC1 (n : nat)
  | MC2 (b : bool)
  | MC3 (t : tree)
  | MC4 (l : list nat)
  | MC5 (p : positive)
  | MC6 (z : Z)
  | MC7 (nt : nested_tree nat)
  | MC8 (nt2 : nested_tree_2 nat bool).
Elpi derive.jsonifiable many_constructors.
Definition test_many_constructors := MC8 (NNode2 [(42, NLeaf2); (7, NNode2 [(13, NLeaf2)] [])] [(true, NLeaf2); (false, NNode2 [] [(true, NLeaf2)])]).
Definition test_many_constructors2 := MC4 [1; 2; 3; 4].
Compute (to_JSON test_many_constructors : JSON).
Compute (from_JSON (to_JSON test_many_constructors) : Result many_constructors string).
Compute (to_JSON test_many_constructors2 : JSON).
Compute (from_JSON (to_JSON test_many_constructors2) : Result many_constructors string).

(* ===== Test 12: Nested type with many nestings *)
Inductive nested_tree_3 (A B C : Type) :=
  | NLeaf3 : nested_tree_3 A B C
  | NNode3 : list (A * list (B * list (C * nested_tree_3 A B C))) -> nested_tree_3 A B C.
Arguments NLeaf3 {A B C}.
Arguments NNode3 {A B C} _.
Elpi derive.jsonifiable nested_tree_3.

Definition test_nested_tree_3 := NNode3 [(42, [(true, [("hello", NLeaf3)])])].
Compute (nested_tree_3_to_json _ _ _ _ _ _ test_nested_tree_3 : JSON).
Compute (nested_tree_3_from_json _ _ _ _ _ _ (nested_tree_3_to_json _ _ _ _ _ _ test_nested_tree_3) : Result (nested_tree_3 nat bool string) string).
