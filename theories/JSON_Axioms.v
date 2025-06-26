From RocqJSON Require Import JSON_Type JSON_Stringification.
From RocqCandy Require Export All.

Definition JSON_from_string (s : string) : Result JSON string.
Admitted.

Axiom JSON_canonical_stringification :
  forall j : JSON, 
  JSON_from_string (JSON_to_string j) = res j.
