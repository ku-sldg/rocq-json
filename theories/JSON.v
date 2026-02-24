(* The Main interface for JSON that exports its sub-properties *)

From RocqJSON Require Import JSON_Error_Strings.
From RocqJSON Require Export JSON_Type JSON_Stringifiable.
From RocqCandy Require Import All.

(* The JSONIFIABLE Class *)
Class Jsonifiable (A : Type) := {
  to_JSON : A -> JSON;
  from_JSON : JSON -> Result A string;
  canonical_jsonification : forall (a : A), from_JSON (to_JSON a) = res a
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

Global Instance Jsonifiable_str_pair {A B : Type} `{Stringifiable A, Stringifiable B} : Jsonifiable (A * B).
eapply Build_Jsonifiable with 
  (to_JSON := str_pair_to_JSON)
  (from_JSON := str_pair_from_JSON).
simpl_json.
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
simpl_json.
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
                               end 
  }.

Global Instance Jsonifiable_nat : Jsonifiable nat := {
  to_JSON   := fun n => JSON_Nat n ;
  from_JSON := fun js => 
                  match js with 
                  | JSON_Nat n => res n 
                  | _ => err (errStr_json_wrong_type "nat" js)
                  end;
  canonical_jsonification := fun n => eq_refl
}.

(* NOTE: This is commented out because it will override TC instances for
Map A B, which is not what we want! A possible (and maybe optimal solution) 
would be to have the Map's be behind module interfaces and then the Jsonifiable
instance shouldn't apply anymore

Global Instance Jsonifiable_list {A} `{Jsonifiable A} : Jsonifiable (list A).
eapply Build_Jsonifiable with
  (to_JSON   := fun l => JSON_Array (map to_JSON l))
  (from_JSON := fun js => 
                  match js with 
                  | JSON_Array l => 
                      result_map from_JSON l
                  | _ => err (errStr_json_wrong_type "list" js)
                  end).
induction a; jsonifiable_hammer.
Qed. *)

(* The List JSONIFIABLE Class *)

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

Global Instance jsonifiable_map_serial_serial (A B : Type) `{Stringifiable A, DecEq A, Stringifiable B} : Jsonifiable (Map A B) :=
  {
    to_JSON   := map_serial_serial_to_JSON;
    from_JSON := map_serial_serial_from_JSON;
    canonical_jsonification := canonical_jsonification_map_serial_serial;
  }.

Global Instance jsonifiable_map_serial_json (A B : Type) `{Stringifiable A, DecEq A, Jsonifiable B} : Jsonifiable (Map A B).
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
induction a; ff with simpl_json.
Defined.

Close Scope string_scope.
