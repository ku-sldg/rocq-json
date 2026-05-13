From RocqCandy Require Import All.
From Stdlib Require Import List.

Import ListNotations.

Inductive JSON :=
| JSON_Object   : Map string JSON -> JSON
| JSON_Array    : list JSON -> JSON
| JSON_String   : string -> JSON
| JSON_Nat      : nat -> JSON
| JSON_Boolean  : bool -> JSON.

Inductive JSON_equiv : JSON -> JSON -> Prop :=
| JSON_equiv_Object : forall (m1 m2 : Map string JSON),
    NoDup (map fst m1) ->
    NoDup (map fst m2) ->
    (forall k, (exists v, lookup k m1 = Some v) <-> (exists v, lookup k m2 = Some v)) ->
    (forall k v1 v2,
      lookup k m1 = Some v1 ->
      lookup k m2 = Some v2 ->
      JSON_equiv v1 v2) ->
    JSON_equiv (JSON_Object m1) (JSON_Object m2)
| JSON_equiv_Object_assoc : forall (m1 m2 : Map string JSON),
    Forall2
      (fun p1 p2 => fst p1 = fst p2 /\ JSON_equiv (snd p1) (snd p2))
      m1 m2 ->
    JSON_equiv (JSON_Object m1) (JSON_Object m2)
| JSON_equiv_Array : forall l1 l2,
    Forall2 JSON_equiv l1 l2 ->
    JSON_equiv (JSON_Array l1) (JSON_Array l2)
| JSON_equiv_String : forall s,
    JSON_equiv (JSON_String s) (JSON_String s)
| JSON_equiv_Nat : forall n,
    JSON_equiv (JSON_Nat n) (JSON_Nat n)
| JSON_equiv_Boolean : forall b,
    JSON_equiv (JSON_Boolean b) (JSON_Boolean b).

Definition depth_js_array (ls:list JSON) (f:JSON -> nat) : nat := 
  fold_right (fun js acc => max acc (f js)) 0 ls.

Definition depth_js_map (m: Map string JSON) (f:JSON -> nat) : nat := 
  fold_right (fun pr acc => max acc (f (snd pr))) 0 m.

Lemma depth_item_leq_array_max : forall (ls:list JSON) (f:JSON -> nat) (js:JSON),
  In js ls -> f js <= depth_js_array ls f.
Proof.
  induction ls; ff with lia;
  find_eapply_lem_hyp (IHls f).
  unfold depth_js_array in *.
  ff with lia.
Qed.

Lemma depth_item_leq_map_max : forall (m : Map string JSON) (f:JSON -> nat) (js:JSON),
  In js (map snd m) -> f js <= depth_js_map m f.
Proof.
  induction m; ff with lia;
  find_eapply_lem_hyp (IHm f); 
  unfold depth_js_map in *; ff with lia.
Qed.

Fixpoint JSON_depth (js:JSON) : nat := 
  match js with
  | JSON_Boolean _ => 1 
  | JSON_String _ => 1 
  | JSON_Nat _ => 1
  | JSON_Array ls => 1 + depth_js_array ls JSON_depth
  | JSON_Object m => 1 + depth_js_map m JSON_depth
  end.

Theorem JSON_rect_better (P : JSON -> Type)
  (fmap : forall m : Map string JSON, 
    (forall (v:JSON), In v (map snd m) -> P v) -> P (JSON_Object m))
  (flist : forall l : list JSON, (forall v, In v l -> P v) -> P (JSON_Array l))
  (fstring : forall s : string, P (JSON_String s))
  (fnat : forall n : nat, P (JSON_Nat n))
  (fbool : forall b : bool, P (JSON_Boolean b)) :
  forall j : JSON, P j.
Proof.
  assert (forall x : JSON, (forall y : JSON, (fun j1 j2 => JSON_depth j1 < JSON_depth j2) y x -> P y) -> P x). {
    intros js F; destruct js eqn:?; eauto.
    - subst; eapply fmap; intros; eapply F; simpl.
      pose proof (depth_item_leq_map_max m JSON_depth v H); lia.
    - subst; eapply flist; intros; eapply F; simpl.
      pose proof (depth_item_leq_array_max l JSON_depth v H); lia.
  }
  assert (well_founded (fun j1 j2 => JSON_depth j1 < JSON_depth j2)). {
    simpl in *.
    eapply Wf_nat.well_founded_ltof.
  }
  eapply well_founded_induction_type; eauto.
Qed.

Theorem JSON_ind_better (P : JSON -> Prop)
  (fmap : forall m : Map string JSON, 
    (forall (v:JSON), In v (map snd m) -> P v) -> P (JSON_Object m))
  (flist : forall l : list JSON, (forall v, In v l -> P v) -> P (JSON_Array l))
  (fstring : forall s : string, P (JSON_String s))
  (fnat : forall n : nat, P (JSON_Nat n))
  (fbool : forall b : bool, P (JSON_Boolean b)) :
  forall j : JSON, P j.
Proof.
  assert (forall x : JSON, (forall y : JSON, (fun j1 j2 => JSON_depth j1 < JSON_depth j2) y x -> P y) -> P x). {
    intros js F; destruct js eqn:?; eauto.
    - subst; eapply fmap; intros; eapply F; simpl.
      pose proof (depth_item_leq_map_max m JSON_depth v H); lia.
    - subst; eapply flist; intros; eapply F; simpl.
      pose proof (depth_item_leq_array_max l JSON_depth v H); lia.
  }
  assert (well_founded (fun j1 j2 => JSON_depth j1 < JSON_depth j2)). {
    simpl in *.
    eapply Wf_nat.well_founded_ltof.
  }
  eapply well_founded_ind; eauto.
Qed.

Theorem JSON_ind_depth (P : JSON -> Prop)
  (f : forall js : JSON,
    (forall js' : JSON, JSON_depth js' < JSON_depth js -> P js') ->
    P js) :
  forall js : JSON, P js.
Proof.
  assert (well_founded (fun j1 j2 => JSON_depth j1 < JSON_depth j2)). {
    simpl in *.
    eapply Wf_nat.well_founded_ltof.
  }
  eapply well_founded_ind; eauto.
Qed.

Lemma JSON_equiv_refl : forall js, JSON_equiv js js.
Proof.
  induction js using JSON_ind_better.
  - eapply JSON_equiv_Object_assoc.
    induction m as [|[k v] rest IHm]; simpl; constructor.
    + simpl.
      split.
      * reflexivity.
      * apply H; simpl; auto.
    + apply IHm. intros v' Hin. apply H. simpl; auto.
  - eapply JSON_equiv_Array.
    induction l as [|x xs IHxs]; simpl; constructor.
    + apply H; simpl; auto.
    + apply IHxs. intros v Hin. apply H; simpl; auto.
  - constructor.
  - constructor.
  - constructor.
Qed.

Definition map_eqb_eqb {A B} `{DecEq A} (dec_eq_b : IDecEq B) : IDecEq (Map A B).
  ref (fix F l1 l2 :=
    match l1, l2 with
    | nil, nil => left eq_refl
    | (k1, v1) :: l1', (k2, v2) :: l2' => 
      _ (dec_eq k1 k2) (dec_eq_b v1 v2) (F l1' l2')
    | _, _ => right _
    end);  try congruence;
  clear F; intros; 
  destruct x, x0, x1; ff;
  try (left; ff; fail);
  try (right; ff; fail).
Defined.

Definition list_eqb_eqb {A} (dec_eq_a : IDecEq A) : IDecEq (list A).
  ref (fix F l1 l2 :=
    match l1, l2 with
    | nil, nil => left _
    | a1 :: l1, a2 :: l2 => 
      _ (dec_eq_a a1 a2) (F l1 l2)
    | _, _ => right _
    end); try congruence; clear F; ff;
    destruct x, x0; ff.
Defined.

Global Instance DecEq_JSON `{DecEq bool, DecEq nat, DecEq string} : DecEq JSON.
  ref (Build_DecEq _ (fix F (j1 j2 : JSON) :=
  match j1, j2 with
  | JSON_Object o1, JSON_Object o2 => _ (map_eqb_eqb F o1 o2)
  | JSON_Array a1, JSON_Array a2 => _ (list_eqb_eqb F a1 a2)
  | JSON_String s1, JSON_String s2 => _ (dec_eq s1 s2)
  | JSON_Nat n1, JSON_Nat n2 => _ (dec_eq n1 n2)
  | JSON_Boolean b1, JSON_Boolean b2 => _ (dec_eq b1 b2)
  | _, _ => right _
  end)); clear F; ff; destruct x; ff.
Defined.
