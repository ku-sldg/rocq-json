From RocqJSON Require Import JSON_Type.
From RocqCandy Require Export All.

Open Scope string_scope.

Fixpoint JSON_to_string 
    `{Stringifiable bool, Stringifiable nat, Stringifiable string} 
    (j : JSON) : string :=
  match j with
  | JSON_Boolean b => to_string b
  | JSON_String s => """" ++ to_string s ++ """"
  | JSON_Nat n => to_string n
  | JSON_Array ls => "[" ++ String.concat ", " (map JSON_to_string ls) ++ "]"
  | JSON_Object m => 
      "{ " ++ String.concat ", " 
      (map (fun p => """" ++ fst p ++ """: " ++ JSON_to_string (snd p)) m) ++ " }"
  end.

Module Testing.
  (* NOTE: We need this because we Opaque-ified nat_to_string, its HEFTY! *)
  Axiom nat_str : Nat_Stringification.nat_to_string 17 = "17".

  Definition test_json : JSON :=
    JSON_Object [("name", (JSON_String "Alice"));
      ("list_test", (JSON_Array [JSON_Boolean true; JSON_String "test_str"; JSON_Nat 17]))].
  Example test : JSON_to_string test_json = "{ ""name"": ""Alice"", ""list_test"": [true, ""test_str"", 17] }".
    simpl.
    erewrite nat_str.
    reflexivity.
  Qed.
End Testing.

Close Scope string_scope.

Definition JSON_from_string (s : string) : Result JSON string.
Admitted.

Axiom JSON_canonical_stringification :
  forall j : JSON, 
  JSON_from_string (JSON_to_string j) = res j.

Global Instance Stringifiable_JSON : Stringifiable JSON := { 
  to_string := JSON_to_string;
  from_string := JSON_from_string;
  canonical_stringification := JSON_canonical_stringification
}.