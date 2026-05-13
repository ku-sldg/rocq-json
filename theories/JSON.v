(* The Main interface for JSON that exports its sub-properties *)

From RocqJSON Require Import JSON_Error_Strings.
From RocqJSON Require Export JSON_Type JSON_Stringifiable.
From RocqCandy Require Import All.
From Stdlib Require Import List String.

Import ListNotations.

Local Open Scope string_scope.

(* The JSONIFIABLE Class *)
Class Jsonifiable (A : Type) := {
  to_JSON : A -> JSON;
  from_JSON : JSON -> Result A string;
  canonical_jsonification : forall (a : A), from_JSON (to_JSON a) = res a;
  reverse_canonical_jsonification :
    forall (js : JSON) (x : A), from_JSON js = res x -> JSON_equiv (to_JSON x) js
}.

Class ReversibleStringifiable (A : Type) `{Stringifiable A} := {
  reverse_canonical_stringification :
    forall (s : string) (x : A), from_string s = res x -> to_string x = s
}.

Global Instance ReversibleStringifiable_string : ReversibleStringifiable string := {
  reverse_canonical_stringification := fun s x H => ltac:(inversion H; subst; reflexivity)
}.

Global Instance ReversibleStringifiable_bool : ReversibleStringifiable bool.
Proof.
  constructor.
  intros s x H.
  destruct x; simpl in *.
  - destruct (String.eqb s "true") eqn:Heq.
    apply String.eqb_eq in Heq; subst; reflexivity.
    destruct (String.eqb s "false"); congruence.
  - destruct (String.eqb s "true") eqn:Htrue; try congruence.
    destruct (String.eqb s "false") eqn:Hfalse; try congruence.
    apply String.eqb_eq in Hfalse; subst; reflexivity.
Qed.

Lemma result_map_reverse_json_equiv {A} `{Jsonifiable A} :
  forall (js : list JSON) (xs : list A),
    result_map from_JSON js = res xs ->
    Forall2 JSON_equiv (map to_JSON xs) js.
Proof.
  induction js; intros xs Hres; simpl in Hres.
  - invc Hres; constructor.
  - destruct (from_JSON a) eqn:Ha; simpl in Hres; try congruence.
    destruct (result_map from_JSON js) eqn:Hs; simpl in Hres; try congruence.
    invc Hres.
    constructor.
    + eapply reverse_canonical_jsonification; eauto.
    + eapply IHjs; eauto.
Qed.

Global Instance Jsonifiable_string : Jsonifiable string := {
  to_JSON := JSON_String;
  from_JSON := fun js => 
                  match js with 
                  | JSON_String s => res s 
                  | _ => err (errStr_json_wrong_type "string" js)
                  end;
  canonical_jsonification := fun s => eq_refl;
  reverse_canonical_jsonification := fun js x H =>
    match js as js' return
      (match js' with
       | JSON_String s => res s
       | _ => err (errStr_json_wrong_type "string" js')
       end = res x -> JSON_equiv (JSON_String x) js') with
    | JSON_String s => fun H' => ltac:(inversion H'; subst; constructor)
    | JSON_Object _ => fun H' => ltac:(congruence)
    | JSON_Array _ => fun H' => ltac:(congruence)
    | JSON_Nat _ => fun H' => ltac:(congruence)
    | JSON_Boolean _ => fun H' => ltac:(congruence)
    end H
}.

Global Instance Stringifiable_Jsonifiable_A {A} `{Jsonifiable A} : Stringifiable A.
ref (Build_Stringifiable _ 
  (fun a => to_string (to_JSON a))
  (fun s => js <- from_string s ;; from_JSON js)
_).
ff with u; erewrite canonical_stringification in *; ff;
erewrite canonical_jsonification in *; ff.
Qed.

(* The JSONIFIABLE Tactics *)
Ltac2 simpl_json0 () :=
  unfold bind in *; simpl in *; intuition;
  repeat (try (rewrite canonical_jsonification in *);
    try (rewrite canonical_stringification in *);
    simpl in *; intuition).
Ltac2 Notation simpl_json := simpl_json0 ().

Ltac2 Notation "solve_json" := 
  simpl_json; try congruence;
  match! goal with
  | [ |- res ?_x = res ?y ] => 
    destruct $y; simpl in *; subst; eauto
  end.

Ltac2 Notation "jsonifiable_hammer" := 
  ff;
  repeat (rewrite canonical_stringification in *); ff;
  repeat (rewrite canonical_jsonification in *); ff.

(* The JSONIFIABLE Class *)

Open Scope map_scope.

Definition JSON_get_Object (key : string) (js : JSON) : Result JSON string :=
  match js with
  | JSON_Object m => 
    match m ![ key ] with
    | Some v => res v 
    | None => err (errStr_json_key_not_found key js) 
    end
  | _ => err (errStr_json_wrong_type key js)
  end.

Definition JSON_get_Array (key : string) (js : JSON) : Result (list JSON) string :=
  match JSON_get_Object key js with
  | res (JSON_Array v) => res v
  | res _ => err (errStr_json_wrong_type key js)
  | _ => err (errStr_json_key_not_found key js)
  end.

Definition JSON_get_string (key : string) (js : JSON) : Result string string :=
  match JSON_get_Object key js with
  | res (JSON_String v) => res v
  | res _ => err (errStr_json_wrong_type key js)
  | _ => err (errStr_json_key_not_found key js)
  end.

Definition JSON_get_bool (key : string) (js : JSON) : Result bool string :=
  match (JSON_get_Object key js) with
  | res (JSON_Boolean v) => res v
  | res _ => err (errStr_json_wrong_type key js)
  | _ => err (errStr_json_key_not_found key js)
  end.

(* The Pair JSONIFIABLE Class *)
Definition str_pair_to_JSON {A B : Type} `{Stringifiable A, Stringifiable B} (v : (A * B)) : JSON :=
  JSON_Array [JSON_String (to_string (fst v)); JSON_String (to_string (snd v))].

Definition str_pair_from_JSON {A B : Type} `{Stringifiable A, Stringifiable B} (js : JSON) : Result (A * B) string :=
  match js with
  | JSON_Array [JSON_String a; JSON_String b] =>
    a <- from_string a ;;
    b <- from_string b ;;
    res (a, b)
  | _ => err (errStr_json_from_pair)
  end.

Global Instance Jsonifiable_str_pair {A B : Type}
    `{Stringifiable A, Stringifiable B,
      ReversibleStringifiable A, ReversibleStringifiable B}
    : Jsonifiable (A * B).
eapply Build_Jsonifiable with 
  (to_JSON := str_pair_to_JSON)
  (from_JSON := str_pair_from_JSON).
- simpl_json.
- intros js [a b] Hres.
  unfold str_pair_to_JSON, str_pair_from_JSON in *; simpl in *.
  destruct js as [m|l|s|n|b0]; try congruence.
  destruct l as [|ja rest0].
  { simpl in Hres; congruence. }
  destruct rest0 as [|jb rest1].
  { destruct ja; simpl in Hres; congruence. }
  destruct rest1 as [|jc rest2].
  2: { destruct ja; simpl in Hres; try congruence;
       destruct jb; simpl in Hres; congruence. }
  simpl in Hres.
  destruct ja as [m1|l1|sa|n1|b1]; simpl in Hres; try congruence.
  destruct jb as [m2|l2|sb|n2|b2]; simpl in Hres; try congruence.
  destruct (from_string sa) eqn:Ha; simpl in Hres; try congruence.
  destruct (from_string sb) eqn:Hb; simpl in Hres; try congruence.
  invc Hres.
  apply JSON_equiv_Array.
  constructor.
  + erewrite reverse_canonical_stringification by eauto. constructor.
  + constructor.
    * erewrite reverse_canonical_stringification by eauto. constructor.
    * constructor.
Defined.


Definition pair_to_JSON {A B : Type} `{Jsonifiable A, Jsonifiable B} (v : (A * B)) : JSON :=
  JSON_Array [(to_JSON (fst v)); (to_JSON (snd v))].

Definition pair_from_JSON {A B : Type} `{Jsonifiable A, Jsonifiable B} (js : JSON) : Result (A * B) string :=
  match js with
  | JSON_Array [a; b] =>
      match (from_JSON a), (from_JSON b) with
      | res a, res b => res (a, b)
      | _, _ => err errStr_json_to_pair
      end
  | _ => err errStr_json_to_pair
  end.

Global Instance Jsonifiable_pair {A B : Type} `{Jsonifiable A, Jsonifiable B} : Jsonifiable (A * B).
eapply Build_Jsonifiable with 
  (to_JSON := pair_to_JSON)
  (from_JSON := pair_from_JSON).
- simpl_json.
- intros js [a b] Hres.
  unfold pair_to_JSON, pair_from_JSON in *; simpl in *.
  destruct js as [m|l|s|n|b0]; try congruence.
  destruct l as [|ja rest0].
  { simpl in Hres; congruence. }
  destruct rest0 as [|jb rest1].
  { simpl in Hres; congruence. }
  destruct rest1 as [|jc rest2].
  2: { simpl in Hres; congruence. }
  simpl in Hres.
  destruct (from_JSON ja) eqn:Ha; simpl in Hres; try congruence.
  destruct (from_JSON jb) eqn:Hb; simpl in Hres; try congruence.
  invc Hres.
  apply JSON_equiv_Array.
  constructor.
  + eapply reverse_canonical_jsonification; eauto.
  + constructor.
    * eapply reverse_canonical_jsonification; eauto.
    * constructor.
Defined.

Global Instance Jsonifiable_bool : Jsonifiable bool :=
  {
    to_JSON   := fun b => JSON_Boolean b ;
    from_JSON := fun js => 
                    match js with 
                    | JSON_Boolean b => res b 
                    | _ => err (errStr_json_wrong_type "bool" js)
                    end;
    canonical_jsonification := fun b => 
                               match b with 
                               | true => eq_refl 
                               | _ => eq_refl 
                               end;
    reverse_canonical_jsonification := fun js x H =>
      match js as js' return
        (match js' with
         | JSON_Boolean b => res b
         | _ => err (errStr_json_wrong_type "bool" js')
         end = res x -> JSON_equiv (JSON_Boolean x) js') with
      | JSON_Boolean b => fun H' => ltac:(inversion H'; subst; constructor)
      | JSON_Object _ => fun H' => ltac:(congruence)
      | JSON_Array _ => fun H' => ltac:(congruence)
      | JSON_String _ => fun H' => ltac:(congruence)
      | JSON_Nat _ => fun H' => ltac:(congruence)
      end H
  }.

Global Instance Jsonifiable_nat : Jsonifiable nat := {
  to_JSON   := fun n => JSON_Nat n ;
  from_JSON := fun js => 
                  match js with 
                  | JSON_Nat n => res n 
                  | _ => err (errStr_json_wrong_type "nat" js)
                  end;
  canonical_jsonification := fun n => eq_refl;
  reverse_canonical_jsonification := fun js x H =>
    match js as js' return
      (match js' with
       | JSON_Nat n => res n
       | _ => err (errStr_json_wrong_type "nat" js')
       end = res x -> JSON_equiv (JSON_Nat x) js') with
    | JSON_Nat n => fun H' => ltac:(inversion H'; subst; constructor)
    | JSON_Object _ => fun H' => ltac:(congruence)
    | JSON_Array _ => fun H' => ltac:(congruence)
    | JSON_String _ => fun H' => ltac:(congruence)
    | JSON_Boolean _ => fun H' => ltac:(congruence)
    end H
}.

(* The List JSONIFIABLE Class.
   Keep this behind the Map encoders: RocqCandy's Map is a list alias, so the
   generic list encoder must not win for Map A B. *)
Global Instance Jsonifiable_list {A} `{Jsonifiable A} : Jsonifiable (list A) | 100.
eapply Build_Jsonifiable with
  (to_JSON   := fun l => JSON_Array (map to_JSON l))
  (from_JSON := fun js => 
                  match js with 
                  | JSON_Array l => 
                      result_map from_JSON l
                  | _ => err (errStr_json_wrong_type "list" js)
                  end).
- induction a; jsonifiable_hammer.
- intros js xs Hres.
  destruct js as [m|l|s|n|b]; simpl in Hres; try congruence.
  apply JSON_equiv_Array.
  eapply result_map_reverse_json_equiv; eauto.
Defined.

Definition option_to_JSON {A : Type} `{Jsonifiable A} (v : option A) : JSON :=
  match v with
  | Some a => JSON_Object [("Some", to_JSON a)]
  | None => JSON_String "None"
  end.

Definition option_from_JSON {A : Type} `{Jsonifiable A} (js : JSON) : Result (option A) string :=
  match js with
  | JSON_String tag =>
      if string_dec tag "None" then res None
      else err err_str_json_unrecognized_constructor
  | JSON_Object [(tag, a)] =>
      if string_dec tag "Some" then
        a <- from_JSON a ;;
        res (Some a)
      else err err_str_json_unrecognized_constructor
  | _ => err err_str_json_no_constructor_name_string
  end.

Global Instance Jsonifiable_option {A : Type} `{Jsonifiable A} : Jsonifiable (option A).
eapply Build_Jsonifiable with
  (to_JSON := option_to_JSON)
  (from_JSON := option_from_JSON).
- destruct a; simpl; jsonifiable_hammer.
- intros js x Hres.
  unfold option_to_JSON, option_from_JSON in *.
  destruct js as [m|l|s|n|b]; simpl in Hres; try congruence.
  + destruct m as [|[tag ja] rest]; simpl in Hres; try congruence.
    destruct rest as [|p rest]; simpl in Hres; try congruence.
    destruct (string_dec tag "Some"); subst; simpl in Hres; try congruence.
    destruct (from_JSON ja) eqn:Ha; simpl in Hres; try congruence.
    invc Hres.
    apply JSON_equiv_Object_assoc.
    constructor.
    * simpl.
      split.
      -- reflexivity.
      -- eapply reverse_canonical_jsonification; eauto.
    * constructor.
  + destruct (string_dec s "None"); subst; try congruence.
    invc Hres; constructor.
Defined.

Definition map_serial_serial_to_JSON {A B : Type} `{Stringifiable A, Stringifiable B, DecEq A} (m : Map A B) : JSON :=
  JSON_Object (
    map (fun '(k, v) => (to_string k, JSON_String (to_string v))) m).

Definition map_serial_serial_from_JSON {A B : Type} `{Stringifiable A, Stringifiable B, DecEq A} (js : JSON) : Result (Map A B) string :=
  match js with
  | JSON_Object m => 
      result_map 
        (fun '(k, v) => 
          match v with
          | JSON_String v' =>
            k' <- from_string k ;;
            v' <- from_string v' ;;
            res (k', v')
          | _ => err (errStr_map_from_json)
          end) m
  | _ => err (errStr_map_from_json)
  end.

Lemma canonical_jsonification_map_serial_serial : forall {A B} `{Stringifiable A, Stringifiable B, DecEq A} (m : Map A B),
  map_serial_serial_from_JSON (map_serial_serial_to_JSON m) = res m.
Proof.
  intuition.
  induction m; ff with u; repeat (rewrite canonical_stringification in *); ff.
Qed.

Lemma reverse_jsonification_map_serial_serial {A B : Type}
    `{Stringifiable A, DecEq A, Stringifiable B,
      ReversibleStringifiable A, ReversibleStringifiable B} :
    forall (js : JSON) (m : Map A B),
    map_serial_serial_from_JSON js = res m ->
    JSON_equiv (map_serial_serial_to_JSON m) js.
Proof.
  intros js out Hres.
  unfold map_serial_serial_from_JSON in Hres.
  destruct js as [m|l|s|n|b]; try congruence.
  unfold map_serial_serial_to_JSON.
  apply JSON_equiv_Object_assoc.
  revert out Hres.
  induction m as [|[k v] rest IH]; intros out Hres; simpl in *.
  - invc Hres. constructor.
  - destruct v as [m0|l0|sv|n0|b0]; simpl in Hres; try congruence.
    destruct (from_string k) eqn:Hk; simpl in Hres; try congruence.
    destruct (from_string sv) eqn:Hv; simpl in Hres; try congruence.
    destruct (result_map
      (fun '(k0, v) =>
        match v with
        | JSON_String v' =>
            k' <- from_string k0;;
            v'0 <- from_string v';;
            res (k', v'0)
        | _ => err errStr_map_from_json
        end) rest) eqn:Hr; simpl in Hres; try congruence.
    invc Hres.
    constructor.
    + simpl.
      split.
      * erewrite reverse_canonical_stringification by eauto. reflexivity.
      * erewrite reverse_canonical_stringification by eauto. constructor.
    + eapply IH; eauto.
Qed.

Global Instance jsonifiable_map_serial_serial (A B : Type)
    `{Stringifiable A, DecEq A, Stringifiable B,
      ReversibleStringifiable A, ReversibleStringifiable B}
    : Jsonifiable (Map A B) :=
  {
    to_JSON   := map_serial_serial_to_JSON;
    from_JSON := map_serial_serial_from_JSON;
    canonical_jsonification := canonical_jsonification_map_serial_serial;
    reverse_canonical_jsonification := reverse_jsonification_map_serial_serial;
  }.

Global Instance jsonifiable_map_serial_json (A B : Type)
    `{Stringifiable A, DecEq A, ReversibleStringifiable A, Jsonifiable B}
    : Jsonifiable (Map A B).
eapply Build_Jsonifiable with (
  to_JSON := (fun m => JSON_Object (
                      map (fun '(k, v) => 
                            (to_string k, to_JSON v)
                          ) m))) 
  (from_JSON := (fun js =>   
                    match js with
                    | JSON_Object m => 
                        result_map 
                          (fun '(k, v) => 
                            k' <- from_string k ;;
                            v' <- from_JSON v ;;
                            res (k', v')) m
                    | _ => err (errStr_map_from_json)
                    end)).
- induction a; ff with simpl_json.
- intros js out Hres.
  destruct js as [m|l|s|n|b]; simpl in Hres; try congruence.
  apply JSON_equiv_Object_assoc.
  revert out Hres.
  induction m as [|[k v] rest IH]; intros out Hres; simpl in *.
  + invc Hres. constructor.
  + destruct (from_string k) eqn:Hk; simpl in Hres; try congruence.
    destruct (from_JSON v) eqn:Hv; simpl in Hres; try congruence.
    destruct (result_map
      (fun '(k0, v0) =>
        k' <- from_string k0;;
        v' <- from_JSON v0;;
        res (k', v')) rest) eqn:Hr; simpl in Hres; try congruence.
    invc Hres.
    constructor.
    * simpl.
      split.
      -- erewrite reverse_canonical_stringification by eauto. reflexivity.
      -- eapply reverse_canonical_jsonification; eauto.
    * eapply IH; eauto.
Defined.

Example Jsonifiable_map_prefers_object_encoder :
  match to_JSON ([("x", 1)] : Map string nat) with
  | JSON_Object _ => true
  | _ => false
  end = true.
Proof. reflexivity. Qed.

Close Scope string_scope.
