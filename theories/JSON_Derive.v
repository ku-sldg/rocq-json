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
Set Typeclasses Depth 5.

Ltac destruct_nesters :=
  repeat match goal with
  | p : prod _ _ |- _ => destruct p; cbn
  end.

(* ===== Database ===== *)
Elpi Db derive.jsonifiable.db lp:{{
  pred jsonifiable-done o:gref.
}}.

(* NOTE: This is called by "jsonifiable.elpi" to solve the main goal of deriving
   JSON_Derive.Jsonifiable for a given inductive type. *)

(* For non-recursive types: no fix needed, just destruct *)
Ltac derive_jsonifiable_proof_norec :=
  intros;
  match goal with
  | v : _ |- _ => revert v; intro v; destruct v
  end;
  cbn;
  repeat (rewrite canonical_jsonification);
  reflexivity.

Set Default Proof Mode "Classic".
Lemma result_map_map {A B C} (g : B -> Result A C) (f : A -> B) 
    (l : list A) (Hrec : forall c, g (f c) = res c) 
    : result_map g (map f l) = res l.
Proof.
  induction l as [| l].
  - reflexivity.
  - cbn.
    rewrite Hrec.
    rewrite IHl.
    reflexivity.
Defined.

Ltac derive_jsonifiable_proof :=
  intros;
  match goal with
  | v : _ |- _ => 
    revert v;
    fix IH_rec 1;
    intro v; destruct v
  end;
  repeat (cbn; try reflexivity;
    match goal with
    | |- context [result_map ?g (map ?f ?l)] =>
      (* This case only really happens for nesting maps,
        thus the alternate case may need to handle some additional
        destruction *)
      erewrite result_map_map; [ | intros; destruct_nesters ]
    | |- context [ from_JSON (to_JSON ?v) ] =>
      repeat (erewrite canonical_jsonification)
    | o : option _ |- _ => destruct o; cbn
    | |- _ => repeat (erewrite &IH_rec)
    end
  ).

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
Definition test_color := Green.
Example test_color_to_JSON :
  to_JSON test_color = JSON_String "Green"
  := eq_refl.
Example test_color_roundtrip :
  from_JSON (to_JSON test_color) = res test_color
  := canonical_jsonification test_color.

(* Constructors with non-recursive arguments (nat is Jsonifiable) ===== *)
Inductive foo := Fa (n : nat) | Fb (m1 m2 : nat).
Elpi derive.jsonifiable foo.
Definition test_foo := Fb 7 13.
Example test_foo_to_JSON :
  to_JSON test_foo = JSON_Object [("Fb", JSON_Object [("m1", JSON_Nat 7); ("m2", JSON_Nat 13)])] 
  := eq_refl.
Example test_foo_roundtrip :
  from_JSON (to_JSON test_foo) = res test_foo 
  := canonical_jsonification test_foo.

(* ===== Test 3: Recursive type ===== *)
Inductive tree := Leaf | Node (l : tree) (n : nat) (r : tree).
Elpi derive.jsonifiable tree.
Definition test_tree := Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf).
Example test_tree_to_JSON :
  to_JSON test_tree =
    JSON_Object [("Node", JSON_Object [
      ("l", to_JSON (Node Leaf 1 Leaf));
      ("n", JSON_Nat 2);
      ("r", to_JSON (Node Leaf 3 Leaf))])]
  := eq_refl.
Example test_tree_roundtrip :
  from_JSON (to_JSON test_tree) = res test_tree
  := canonical_jsonification test_tree.

(* ===== Test 4: Parametric recursive type ===== *)
Inductive jtree (A : Type) :=
  | JLeaf : jtree
  | JNode : A -> jtree -> jtree -> jtree.
Arguments JLeaf {A}.
Arguments JNode {A} _ _ _.
Elpi derive.jsonifiable jtree.
Definition test_jtree := JNode 42 JLeaf JLeaf.
Example test_jtree_to_JSON :
  to_JSON test_jtree =
    JSON_Object [("JNode", JSON_Object [
      ("v", JSON_Nat 42);
      ("j1", JSON_String "JLeaf");
      ("j2", JSON_String "JLeaf")])]
  := eq_refl.
Example test_jtree_roundtrip :
  from_JSON (to_JSON test_jtree) = res test_jtree
  := canonical_jsonification test_jtree.

(* Testing with Uniform Inductive Parameters disabled as well *)
Unset Uniform Inductive Parameters.

(* ===== Test 5: More complex parametric recursive type ===== *)
Inductive ab_tree (A B : Type) :=
  | ABLeaf : ab_tree A B
  | ABNode (a : A) (tree' : ab_tree A B) (b : B) : ab_tree A B.
Arguments ABLeaf {A B}.
Arguments ABNode {A B} _ _ _.
Elpi derive.jsonifiable ab_tree.
Definition test_ab_tree := ABNode 1 ABLeaf true.
Example test_ab_tree_to_JSON :
  to_JSON test_ab_tree =
    JSON_Object [("ABNode", JSON_Object [
      ("a", JSON_Nat 1);
      ("tree'", JSON_String "ABLeaf");
      ("b", JSON_Boolean true)])]
  := eq_refl.
Example test_ab_tree_roundtrip :
  from_JSON (to_JSON test_ab_tree) = res test_ab_tree
  := canonical_jsonification test_ab_tree.

(* ===== Test 6: Record type ===== *)
Record test_rec := {
  a : nat;
  b : bool;
  c : tree
}.
Elpi derive.jsonifiable test_rec.
Definition test_test_rec := {| a := 42; b := true; c := Node Leaf 1 Leaf |}.
Example test_test_rec_to_JSON :
  to_JSON test_test_rec =
    JSON_Object [
      ("a", JSON_Nat 42);
      ("b", JSON_Boolean true);
      ("c", to_JSON (Node Leaf 1 Leaf))]
  := eq_refl.
Example test_test_rec_roundtrip :
  from_JSON (to_JSON test_test_rec) = res test_test_rec
  := canonical_jsonification test_test_rec.

(* ===== Test 7: Polymorphic Record type ===== *)
Record prec (A B : Type) := {
  pa : A;
  pb : B;
  pc : ab_tree A B
}.
Elpi derive.jsonifiable prec.
Definition test_prec :=
  {| pa := 42; pb := true; pc := (ABNode 0 ABLeaf false) |}.
Example test_prec_to_JSON :
  to_JSON test_prec =
    JSON_Object [
      ("pa", JSON_Nat 42);
      ("pb", JSON_Boolean true);
      ("pc", to_JSON (ABNode 0 ABLeaf false))]
  := eq_refl.
Example test_prec_roundtrip :
  from_JSON (to_JSON test_prec) = res test_prec
  := canonical_jsonification test_prec.

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
Example test_nested_tree_to_JSON :
  to_JSON test_nested_tree =
    JSON_Object [("NNode", JSON_Object [
      ("l", JSON_Array [
        JSON_Array [JSON_Nat 42; JSON_String "NLeaf"];
        JSON_Array [JSON_Nat 7; to_JSON (NNode [(13, NLeaf)] : nested_tree nat)]])])]
  := eq_refl.
Example test_nested_tree_roundtrip :
  from_JSON (to_JSON test_nested_tree) = res test_nested_tree
  := canonical_jsonification test_nested_tree.

(* ===== Test 10: Complex Nested Type ===== *)
Inductive nested_tree_2 (A B : Type) :=
  | NLeaf2 : nested_tree_2 A B
  | NNode2 : list (A * nested_tree_2 A B) -> list (B * nested_tree_2 A B) -> nested_tree_2 A B.
Arguments NLeaf2 {A B}.
Arguments NNode2 {A B} _ _.
Elpi derive.jsonifiable nested_tree_2.

Definition test_nested_tree_2 := NNode2 [(42, NLeaf2); (7, NNode2 [(13, NLeaf2)] [])] [(true, NLeaf2); (false, NNode2 [] [(true, NLeaf2)])].
Example test_nested_tree_2_to_JSON :
  to_JSON test_nested_tree_2 =
    JSON_Object [("NNode2", JSON_Object [
      ("l1", JSON_Array [
        JSON_Array [JSON_Nat 42; JSON_String "NLeaf2"];
        JSON_Array [JSON_Nat 7; to_JSON (NNode2 [(13, NLeaf2)] [] : nested_tree_2 nat bool)]]);
      ("l2", JSON_Array [
        JSON_Array [JSON_Boolean true; JSON_String "NLeaf2"];
        JSON_Array [JSON_Boolean false; to_JSON (NNode2 [] [(true, NLeaf2)] : nested_tree_2 nat bool)]])])]
  := eq_refl.
Example test_nested_tree_2_roundtrip :
  from_JSON (to_JSON test_nested_tree_2) = res test_nested_tree_2
  := canonical_jsonification test_nested_tree_2.

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
Example test_many_constructors_to_JSON :
  to_JSON test_many_constructors =
    JSON_Object [("MC8", JSON_Object [("nt2", to_JSON test_nested_tree_2)])]
  := eq_refl.
Example test_many_constructors_roundtrip :
  from_JSON (to_JSON test_many_constructors) = res test_many_constructors
  := canonical_jsonification test_many_constructors.
Example test_many_constructors2_to_JSON :
  to_JSON test_many_constructors2 =
    JSON_Object [("MC4", JSON_Object [
      ("l", JSON_Array [JSON_Nat 1; JSON_Nat 2; JSON_Nat 3; JSON_Nat 4])])]
  := eq_refl.
Example test_many_constructors2_roundtrip :
  from_JSON (to_JSON test_many_constructors2) = res test_many_constructors2
  := canonical_jsonification test_many_constructors2.

(* ===== Test 12: Non-recursive option fields ===== *)
Inductive option_payload :=
  | OPNone (n : option nat)
  | OPMix (n : option nat) (b : option bool).
Elpi derive.jsonifiable option_payload.

Definition test_option_payload := OPMix (Some 5) None.
Example test_option_payload_to_JSON :
  to_JSON test_option_payload =
    JSON_Object [("OPMix", JSON_Object [
      ("n", to_JSON (Some 5));
      ("b", to_JSON (None : option bool))])]
  := eq_refl.
Example test_option_payload_roundtrip :
  from_JSON (to_JSON test_option_payload) = res test_option_payload.
Proof. exact (canonical_jsonification test_option_payload). Qed.

(* ===== Test 13: Record option fields ===== *)
Record option_rec := {
  or_n : option nat;
  or_t : option tree
}.
Elpi derive.jsonifiable option_rec.

Definition test_option_rec :=
  {| or_n := Some 42; or_t := Some (Node Leaf 1 Leaf) |}.
Example test_option_rec_to_JSON :
  to_JSON test_option_rec =
    JSON_Object [
      ("or_n", to_JSON (Some 42));
      ("or_t", to_JSON (Some (Node Leaf 1 Leaf)))]
  := eq_refl.
Example test_option_rec_roundtrip :
  from_JSON (to_JSON test_option_rec) = res test_option_rec.
Proof. exact (canonical_jsonification test_option_rec). Qed.

(* ===== Test 14: Recursive option field ===== *)
Inductive nested_tree_3 (A B : Type) :=
  | NLeaf3 : nested_tree_3 A B
  | NNode3 : A -> B -> option (nested_tree_3 A B) -> nested_tree_3 A B.
Arguments NLeaf3 {A B}.
Arguments NNode3 {A B} _ _ _.
Elpi derive.jsonifiable nested_tree_3.

Definition test_nested_tree_3 : nested_tree_3 nat bool :=
  NNode3 43 true (Some (NNode3 7 false None)).
Example test_nested_tree_3_to_JSON :
  to_JSON test_nested_tree_3 =
    JSON_Object [("NNode3", JSON_Object [
      ("v1", JSON_Nat 43);
      ("v2", JSON_Boolean true);
      ("o", JSON_Object [("Some", JSON_Object [
        ("v", to_JSON (NNode3 7 false None : nested_tree_3 nat bool))])])])]
  := eq_refl.
Example test_nested_tree_3_roundtrip :
  from_JSON (to_JSON test_nested_tree_3) = res test_nested_tree_3.
Proof. exact (canonical_jsonification test_nested_tree_3). Qed.

(* ===== Test 15: Recursive option inside nested lists/products ===== *)
Inductive nested_tree_4 (A B C : Type) :=
  | NLeaf4 : nested_tree_4 A B C
  | NNode4 : list (A * option (nested_tree_4 A B C)) -> nested_tree_4 A B C.
Arguments NLeaf4 {A B C}.
Arguments NNode4 {A B C} _.
Elpi derive.jsonifiable nested_tree_4.

Definition test_nested_tree_4 : nested_tree_4 nat bool string :=
  NNode4 [(42, Some NLeaf4); (7, Some (NNode4 [(13, None)]))].
Example test_nested_tree_4_to_JSON :
  to_JSON test_nested_tree_4 =
    JSON_Object [("NNode4", JSON_Object [
      ("l", JSON_Array [
        JSON_Array [
          JSON_Nat 42;
          JSON_Object [("Some", JSON_Object [("v", JSON_String "NLeaf4")])]];
        JSON_Array [
          JSON_Nat 7;
          JSON_Object [("Some", JSON_Object [
            ("v", to_JSON (NNode4 [(13, None)] : nested_tree_4 nat bool string))])]]])])]
  := eq_refl.
Example test_nested_tree_4_roundtrip :
  from_JSON (to_JSON test_nested_tree_4) = res test_nested_tree_4.
Proof. exact (canonical_jsonification test_nested_tree_4). Qed.
