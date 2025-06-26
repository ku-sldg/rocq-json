From RocqJSON Require Import JSON_Type JSON_Stringification JSON_Axioms.
From RocqCandy Require Export All.

Global Instance Stringifiable_JSON : Stringifiable JSON := { 
  to_string := JSON_to_string;
  from_string := JSON_from_string;
  canonical_stringification := JSON_canonical_stringification
}.