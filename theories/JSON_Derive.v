From elpi Require Import elpi.
From elpi Require Import derive.
From elpi Require Import derive.std.

From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From rocq_json_derivers Extra Dependency "jsonifiable.elpi" as jsonifiable.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.


From RocqJSON Require Export JSON JSON_Error_Strings.
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

Lemma result_map_reverse_JSON_equiv_custom {A}
    (from : JSON -> Result A string) (to : A -> JSON) :
    (forall js x, from js = res x -> JSON_equiv (to x) js) ->
    forall js xs,
      result_map from js = res xs ->
      Forall2 JSON_equiv (map to xs) js.
Proof.
  intros Helt js.
  induction js as [|j js IH]; intros xs Hmap; cbn in Hmap.
  - inversion Hmap; subst; constructor.
  - destruct (from j) eqn:Hj; cbn in Hmap; try discriminate.
    destruct (result_map from js) eqn:Hjs; cbn in Hmap; try discriminate.
    inversion Hmap; subst; clear Hmap.
    cbn.
    constructor.
    + eapply Helt; eauto.
    + eapply IH; eauto.
Qed.

Lemma result_map_reverse_JSON_equiv_custom_in {A}
    (from : JSON -> Result A string) (to : A -> JSON) :
    forall js xs,
      result_map from js = res xs ->
      (forall js0 x, In js0 js -> from js0 = res x -> JSON_equiv (to x) js0) ->
      Forall2 JSON_equiv (map to xs) js.
Proof.
  induction js as [|j js IH]; intros xs Hmap Helt; cbn in Hmap.
  - inversion Hmap; subst; constructor.
  - destruct (from j) eqn:Hj; cbn in Hmap; try discriminate.
    destruct (result_map from js) eqn:Hjs; cbn in Hmap; try discriminate.
    inversion Hmap; subst; clear Hmap.
    cbn.
    constructor.
    + eapply Helt; eauto. left; reflexivity.
    + eapply IH; eauto.
      intros js0 x Hin Hfrom.
      eapply Helt; eauto. right; assumption.
Qed.

Lemma result_map_reverse_JSON_equiv_pair_array_custom {A B}
    (fromA : JSON -> Result A string) (toA : A -> JSON)
    (fromB : JSON -> Result B string) (toB : B -> JSON)
    (err_msg : string) :
    forall js xs,
      result_map
        (fun js0 =>
          match js0 with
          | JSON_Array [ajs; bjs] =>
              av <- fromA ajs ;;
              bv <- fromB bjs ;;
              res (av, bv)
          | _ => err err_msg
          end) js = res xs ->
      (forall ajs a, fromA ajs = res a -> JSON_equiv (toA a) ajs) ->
      (forall ajs bjs b,
        In (JSON_Array [ajs; bjs]) js ->
        fromB bjs = res b ->
        JSON_equiv (toB b) bjs) ->
      Forall2 JSON_equiv
        (map (fun p => JSON_Array [toA (fst p); toB (snd p)]) xs) js.
Proof.
  induction js as [|j js IH]; intros xs Hmap HA HB; cbn in Hmap.
  - inversion Hmap; subst; constructor.
  - destruct j as [|arr| | |]; cbn in Hmap; try discriminate.
    destruct arr as [|ajs arr]; cbn in Hmap; try discriminate.
    destruct arr as [|bjs arr]; cbn in Hmap; try discriminate.
    destruct arr as [|extra arr]; cbn in Hmap; try discriminate.
    destruct (fromA ajs) eqn:Ha; cbn in Hmap; try discriminate.
    destruct (fromB bjs) eqn:Hb; cbn in Hmap; try discriminate.
    destruct (result_map
      (fun js0 =>
        match js0 with
        | JSON_Array [ajs0; bjs0] =>
            av <- fromA ajs0;;
            bv <- fromB bjs0;;
            res (av, bv)
        | _ => err err_msg
        end) js) eqn:Hr; cbn in Hmap; try discriminate.
    inversion Hmap; subst; clear Hmap.
    cbn.
    constructor.
    + apply JSON_equiv_Array.
      constructor.
      * eapply HA; eauto.
      * constructor.
        -- eapply HB; eauto. left; reflexivity.
        -- constructor.
    + eapply IH; eauto.
      intros ajs0 bjs0 bval Hin Hfrom.
      eapply HB.
      * right; exact Hin.
      * exact Hfrom.
Qed.

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

Ltac json_reverse_cleanup_eq H :=
  lazymatch type of H with
  | ?lhs = _ =>
      lazymatch lhs with
      | context [if String.eqb ?x ?y then _ else _] =>
          destruct (String.eqb x y) eqn:?; cbn in H; try discriminate;
          try match goal with
          | Heq : String.eqb x y = true |- _ =>
              apply String.eqb_eq in Heq; subst
          end
      | context [string_dec ?x ?y] =>
          destruct (string_dec x y); subst; cbn in H; try discriminate
      | context [bind ?r ?f] =>
          destruct r eqn:?; cbn in H; try discriminate
      | context [match ?r with res _ => _ | err _ => _ end] =>
          destruct r eqn:?; cbn in H; try discriminate
      | context [match ?j with
                 | JSON_Object _ => _
                 | JSON_Array _ => _
                 | JSON_String _ => _
                 | JSON_Nat _ => _
                 | JSON_Boolean _ => _
                 end] =>
          destruct j; cbn in H; try discriminate
      | context [match ?o with Some _ => _ | None => _ end] =>
          destruct o eqn:?; cbn in H; try discriminate
      | context [match ?l with nil => _ | cons _ _ => _ end] =>
          destruct l; cbn in H; try discriminate
      | context [match ?n with O => _ | S _ => _ end] =>
          destruct n; cbn in H; try discriminate
      | context [match ?s with EmptyString => _ | String _ _ => _ end] =>
          destruct s; cbn in H; try discriminate
      | context [match ?a with Ascii _ _ _ _ _ _ _ _ => _ end] =>
          destruct a; cbn in H; try discriminate
      | context [match ?b with true => _ | false => _ end] =>
          destruct b; cbn in H; try discriminate
      end
  end.

Ltac json_reverse_cleanup :=
  repeat match goal with
  | H : err _ = res _ |- _ => discriminate H
  | H : res _ = res _ |- _ => inversion H; subst; clear H
  | H : None = Some _ |- _ => discriminate H
  | H : Some _ = Some _ |- _ => inversion H; subst; clear H
  | H : _ = res _ |- _ => json_reverse_cleanup_eq H
  | H : _ = err _ |- _ => json_reverse_cleanup_eq H
  | H : _ = Some _ |- _ => json_reverse_cleanup_eq H
  | o : option _ |- _ => destruct o; cbn in *
  | p : prod _ _ |- _ => destruct p; cbn in *
  end.

Ltac solve_json_decode :=
  cbn;
  repeat match goal with
  | H : ?lhs = res ?x |- context [?lhs] => rewrite H
  | H : ?lhs = err ?e |- context [?lhs] => rewrite H
  end;
  reflexivity.

Ltac solve_json_depth :=
  cbn in *;
  repeat match goal with
  | |- context [match ?n with O => _ | S _ => _ end] =>
      destruct n eqn:?; cbn in *
  | H : context [match ?n with O => _ | S _ => _ end] |- _ =>
      destruct n eqn:?; cbn in *
  end;
  pose proof Nat.le_max_l;
  pose proof Nat.le_max_r;
  lia.

Ltac solve_json_equiv_by_induction :=
  match goal with
  | IH : forall v : JSON, _ -> forall x, ?from v = res x -> JSON_equiv (?to x) v
    |- JSON_equiv ?lhs ?js =>
      solve [
        let x := fresh "x" in
        let Hfrom := fresh "Hfrom" in
        let Hlhs := fresh "Hlhs" in
        assert (exists x, from js = res x /\ lhs = to x) as [x [Hfrom Hlhs]]
          by (solve [eexists; split; [solve_json_decode | reflexivity]]);
        rewrite Hlhs;
        refine (IH js _ x Hfrom);
        solve [cbn; eauto]
      ]
  end.

Ltac solve_json_equiv :=
  match goal with
  | |- JSON_equiv (JSON_String _) (JSON_String _) => constructor
  | |- JSON_equiv (JSON_Nat _) (JSON_Nat _) => constructor
  | |- JSON_equiv (JSON_Boolean _) (JSON_Boolean _) => constructor
  | H : from_JSON ?js = res ?x |- JSON_equiv (to_JSON ?x) ?js =>
      eapply reverse_canonical_jsonification; eauto
  | IH : forall js' : JSON, JSON_depth js' < ?bound ->
      forall x, ?from js' = res x -> JSON_equiv (?to x) js',
    H : ?from ?js = res ?x |- JSON_equiv (?to ?x) ?js =>
      solve [eapply IH; [solve_json_depth | eassumption]]
  | H : ?from ?js = res ?x |- JSON_equiv (?to ?x) ?js =>
      progress (cbn in H; json_reverse_cleanup; cbn; json_reverse_cleanup);
      solve_json_equiv
  | |- JSON_equiv
        (JSON_Object
          [(?ctor, JSON_Object
            [(?k1, JSON_Array (map ?to1 ?xs1));
             (?k2, JSON_Array (map ?to2 ?xs2))])])
        (JSON_Object
          [(?ctor, JSON_Object
            [(?k1, JSON_Array ?js1);
             (?k2, JSON_Array ?js2)])]) =>
      match goal with
      | H1 : result_map ?from1 ?js1_h = res ?xs1_h |- _ =>
      constr_eq js1_h js1;
      constr_eq xs1_h xs1;
      match goal with
      | H2 : result_map ?from2 ?js2_h = res ?xs2_h |- _ =>
      constr_eq js2_h js2;
      constr_eq xs2_h xs2;
      apply JSON_equiv_Object_assoc;
      constructor;
      [cbn; split;
       [reflexivity
       | apply JSON_equiv_Object_assoc;
         constructor;
         [cbn; split;
          [reflexivity
          | apply JSON_equiv_Array;
            eapply result_map_reverse_JSON_equiv_pair_array_custom;
            [exact H1
            | intros; eapply reverse_canonical_jsonification; eauto
            | let ja := fresh "ja" in
              let jb := fresh "jb" in
              let x := fresh "x" in
              let Hin := fresh "Hin" in
              let Hfrom := fresh "Hfrom" in
              intros ja jb x Hin Hfrom;
              match type of Hin with
              | In (JSON_Array [ja; jb]) ?container =>
                  pose proof (depth_item_leq_array_max container JSON_depth (JSON_Array [ja; jb]) Hin)
              end;
              pose proof (depth_item_leq_array_max [ja; jb] JSON_depth jb ltac:(simpl; auto));
              match goal with
              | IH : forall js' : JSON, JSON_depth js' < ?bound ->
                  forall x, ?from js' = res x -> JSON_equiv (?to x) js'
                |- JSON_equiv (?to ?x) jb =>
                  eapply IH; [solve_json_depth | exact Hfrom]
              | _ => solve_json_equiv
              end]]
         | constructor;
           [cbn; split;
            [reflexivity
            | apply JSON_equiv_Array;
              eapply result_map_reverse_JSON_equiv_pair_array_custom;
              [exact H2
              | intros; eapply reverse_canonical_jsonification; eauto
              | let ja := fresh "ja" in
                let jb := fresh "jb" in
                let x := fresh "x" in
                let Hin := fresh "Hin" in
                let Hfrom := fresh "Hfrom" in
                intros ja jb x Hin Hfrom;
                match type of Hin with
                | In (JSON_Array [ja; jb]) ?container =>
                    pose proof (depth_item_leq_array_max container JSON_depth (JSON_Array [ja; jb]) Hin)
                end;
                pose proof (depth_item_leq_array_max [ja; jb] JSON_depth jb ltac:(simpl; auto));
                match goal with
                | IH : forall js' : JSON, JSON_depth js' < ?bound ->
                    forall x, ?from js' = res x -> JSON_equiv (?to x) js'
                  |- JSON_equiv (?to ?x) jb =>
                    eapply IH; [solve_json_depth | exact Hfrom]
                | _ => solve_json_equiv
                end]]
           | constructor]]]
      | constructor]
      end
      end
  | |- JSON_equiv (JSON_Array (map ?to ?xs)) (JSON_Array ?js) =>
      match goal with
      | Hmap : result_map ?from ?js_h = res ?xs_h |- _ =>
      constr_eq js_h js;
      constr_eq xs_h xs;
      apply JSON_equiv_Array;
      first
      [ eapply (@result_map_reverse_JSON_equiv_custom_in _ from to);
        [exact Hmap
        | let js0 := fresh "js0" in
          let x := fresh "x" in
          let Hin := fresh "Hin" in
          let Helt := fresh "Helt" in
          intros js0 x Hin Helt;
          pose proof (depth_item_leq_array_max js JSON_depth js0 Hin);
          cbn in Helt; json_reverse_cleanup; cbn; json_reverse_cleanup; cbn;
          solve_json_equiv]
      | eapply result_map_reverse_JSON_equiv_pair_array_custom;
        [exact Hmap
        | intros; eapply reverse_canonical_jsonification; eauto
        | let ja := fresh "ja" in
          let jb := fresh "jb" in
          let x := fresh "x" in
          let Hin := fresh "Hin" in
          let Hfrom := fresh "Hfrom" in
          intros ja jb x Hin Hfrom;
          match type of Hin with
          | In (JSON_Array [ja; jb]) ?container =>
              pose proof (depth_item_leq_array_max container JSON_depth (JSON_Array [ja; jb]) Hin)
          end;
          pose proof (depth_item_leq_array_max [ja; jb] JSON_depth jb ltac:(simpl; auto));
          match goal with
          | IH : forall js' : JSON, JSON_depth js' < ?bound ->
              forall x, ?from js' = res x -> JSON_equiv (?to x) js'
            |- JSON_equiv (?to ?x) jb =>
              eapply IH; [solve_json_depth | exact Hfrom]
          | _ => solve_json_equiv
          end]
      | eapply (@result_map_reverse_JSON_equiv_custom_in _ from to);
        [exact Hmap
        | intros js0 ? Hin Helt;
          destruct js0 as [|arr| | |]; cbn in Helt; try discriminate;
          destruct arr as [|ja arr]; cbn in Helt; try discriminate;
          destruct arr as [|jb arr]; cbn in Helt; try discriminate;
          destruct arr as [|jextra arr]; cbn in Helt; try discriminate;
          json_reverse_cleanup; cbn; json_reverse_cleanup; cbn;
          match type of Hin with
          | In (JSON_Array [ja; jb]) ?container =>
              pose proof (depth_item_leq_array_max container JSON_depth (JSON_Array [ja; jb]) Hin)
          end;
          pose proof (depth_item_leq_array_max [ja; jb] JSON_depth jb ltac:(simpl; auto));
          apply JSON_equiv_Array;
          constructor;
          [eapply reverse_canonical_jsonification; eauto
          | constructor; [solve_json_equiv | constructor]]]]
      end
  | |- JSON_equiv (JSON_Array _) (JSON_Array _) =>
      apply JSON_equiv_Array; solve_json_forall2
  | |- JSON_equiv (JSON_Object _) (JSON_Object _) =>
      apply JSON_equiv_Object_assoc; solve_json_forall2
  | |- JSON_equiv ?js ?js =>
      apply JSON_equiv_refl
  end
with solve_json_forall2 :=
  match goal with
  | |- Forall2 JSON_equiv (map ?to ?xs) ?js =>
      match goal with
      | Hmap : result_map ?from ?js_h = res ?xs_h |- _ =>
      constr_eq js_h js;
      constr_eq xs_h xs;
      first
      [ eapply (@result_map_reverse_JSON_equiv_custom_in _ from to);
        [exact Hmap
        | let js0 := fresh "js0" in
          let x := fresh "x" in
          let Hin := fresh "Hin" in
          let Helt := fresh "Helt" in
          intros js0 x Hin Helt;
          pose proof (depth_item_leq_array_max js JSON_depth js0 Hin);
          cbn in Helt; json_reverse_cleanup; cbn; json_reverse_cleanup; cbn;
          solve_json_equiv]
      | eapply result_map_reverse_JSON_equiv_pair_array_custom;
        [exact Hmap
        | intros; eapply reverse_canonical_jsonification; eauto
        | let ja := fresh "ja" in
          let jb := fresh "jb" in
          let x := fresh "x" in
          let Hin := fresh "Hin" in
          let Hfrom := fresh "Hfrom" in
          intros ja jb x Hin Hfrom;
          match type of Hin with
          | In (JSON_Array [ja; jb]) ?container =>
              pose proof (depth_item_leq_array_max container JSON_depth (JSON_Array [ja; jb]) Hin)
          end;
          pose proof (depth_item_leq_array_max [ja; jb] JSON_depth jb ltac:(simpl; auto));
          match goal with
          | IH : forall js' : JSON, JSON_depth js' < ?bound ->
              forall x, ?from js' = res x -> JSON_equiv (?to x) js'
            |- JSON_equiv (?to ?x) jb =>
              eapply IH; [solve_json_depth | exact Hfrom]
          | _ => solve_json_equiv
          end]
      | eapply (@result_map_reverse_JSON_equiv_custom_in _ from to);
        [exact Hmap
        | intros js0 ? Hin Helt;
          destruct js0 as [|arr| | |]; cbn in Helt; try discriminate;
          destruct arr as [|ja arr]; cbn in Helt; try discriminate;
          destruct arr as [|jb arr]; cbn in Helt; try discriminate;
          destruct arr as [|jextra arr]; cbn in Helt; try discriminate;
          json_reverse_cleanup; cbn; json_reverse_cleanup; cbn;
          match type of Hin with
          | In (JSON_Array [ja; jb]) ?container =>
              pose proof (depth_item_leq_array_max container JSON_depth (JSON_Array [ja; jb]) Hin)
          end;
          pose proof (depth_item_leq_array_max [ja; jb] JSON_depth jb ltac:(simpl; auto));
          apply JSON_equiv_Array;
          constructor;
          [eapply reverse_canonical_jsonification; eauto
          | constructor; [solve_json_equiv | constructor]]]]
      end
  | |- Forall2 JSON_equiv [] [] => constructor
  | |- Forall2 JSON_equiv (_ :: _) (_ :: _) =>
      constructor; [solve_json_equiv | solve_json_forall2]
  | |- Forall2 (fun p1 p2 => fst p1 = fst p2 /\ JSON_equiv (snd p1) (snd p2)) [] [] =>
      constructor
  | |- Forall2 (fun p1 p2 => fst p1 = fst p2 /\ JSON_equiv (snd p1) (snd p2)) (_ :: _) (_ :: _) =>
      constructor;
      [cbn; split; [reflexivity | solve_json_equiv]
      | solve_json_forall2]
  end
with solve_json_result_map :=
  match goal with
  | H : result_map ?from ?js = res ?xs |- Forall2 JSON_equiv (map ?to ?xs) ?js =>
      generalize dependent xs;
      induction js as [|j js IH]; intros xs Hmap; cbn in Hmap;
      [inversion Hmap; subst; clear Hmap; constructor
      | destruct (from j) eqn:?; cbn in Hmap; try discriminate;
        destruct (result_map from js) eqn:?; cbn in Hmap; try discriminate;
        inversion Hmap; subst; clear Hmap; cbn;
        constructor;
        [cbn; json_reverse_cleanup; cbn; json_reverse_cleanup; solve_json_equiv
        | match goal with
          | Hstrong : forall js' : JSON, JSON_depth js' < ?bound ->
              forall v, ?from_rec js' = res v -> JSON_equiv (?to_rec v) js' |- _ =>
              eapply IH;
              [intros js' Hlt v Hdec;
               eapply Hstrong; [cbn in *; lia | exact Hdec]
              | eauto]
          end]]
  end.

Ltac derive_jsonifiable_reverse_proof :=
  repeat match goal with
  | |- forall _ : JSON, _ => fail 1
  | |- forall _ : _, _ => intro
  end;
  intros js;
  induction js using JSON_ind_better;
  intros x H;
  cbn in H;
  json_reverse_cleanup;
  cbn;
  json_reverse_cleanup;
  solve_json_equiv.

Ltac derive_jsonifiable_reverse_proof_safe :=
  repeat match goal with
  | |- forall _ : JSON, _ => fail 1
  | |- forall _ : _, _ => intro
  end;
  try intros js;
  try match goal with
  | js : JSON |- _ => induction js using JSON_ind_depth
  end;
  try match goal with
  | js : JSON |- _ => destruct js
  end;
  try intros x Hdec;
  try match goal with
  | Hdec : _ = res _ |- _ => cbn in Hdec
  end;
  try json_reverse_cleanup;
  try cbn;
  try json_reverse_cleanup;
  try solve_json_equiv.

Ltac derive_jsonifiable_reverse_proof_pure_enum :=
  intros js x Hdec;
  destruct js; cbn in Hdec; try discriminate;
  json_reverse_cleanup; constructor.

Ltac derive_jsonifiable_reverse_proof_norec :=
  repeat match goal with
  | |- forall _ : JSON, _ => fail 1
  | |- forall _ : _, _ => intro
  end;
  intros js x Hdec;
  destruct js; cbn in Hdec; try discriminate;
  json_reverse_cleanup;
  cbn;
  json_reverse_cleanup;
  solve_json_equiv.

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
