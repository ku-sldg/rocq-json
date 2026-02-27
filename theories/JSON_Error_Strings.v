From Stdlib Require Import String.
From RocqJSON Require Import JSON_Type JSON_Stringifiable.

Local Open Scope string_scope.

(* JSON Converter Strings *)
Definition errStr_json_to_manifest_set := "errStr_json_to_manifest_set".
Opaque errStr_json_to_manifest_set.

Definition errStr_json_to_map := "errStr_json_to_map".
Opaque errStr_json_to_map.

Definition errStr_json_to_id_type := "errStr_json_to_id_type".
Opaque errStr_json_to_id_type.

Definition errStr_json_to_manifest := "errStr_json_to_manifest".
Opaque errStr_json_to_manifest.

Definition errStr_json_to_ASP_Locator := "errStr_json_to_ASP_Locator".
Opaque errStr_json_to_ASP_Locator.

Definition errStr_json_to_am_lib := "errStr_json_to_am_lib".
Opaque errStr_json_to_am_lib.

Definition errStr_json_to_pair : string := "errStr_json_to_pair".
Opaque errStr_json_to_pair.

Definition errStr_map_from_json := "errStr_map_from_json".
Opaque errStr_map_from_json.

Definition errStr_json_from_pair := "Error converting pair from JSON".
Opaque errStr_json_from_pair.

(* The JSONIFIABLE Class for Stringifiable types *)
Definition str_json_key_prefix := "JSON: Key: '".
Opaque str_json_key_prefix.
Definition str_not_found := " not found in JSON: '".
Opaque str_not_found.
Definition str_had_wrong_type := " had the wrong type in JSON: '".

Definition errStr_json_key_not_found (key : string) (js : JSON) := 
 str_json_key_prefix ++ key ++ str_not_found ++ (to_string js) ++ "'".
Opaque errStr_json_key_not_found.

Definition errStr_json_wrong_type (key : string) (js : JSON) := 
  str_json_key_prefix ++ key ++ str_had_wrong_type ++ (to_string js) ++ "'".
Opaque errStr_json_wrong_type.

Definition err_str_json_nat := "Error converting JSON to nat: JSON was not a nat".
Opaque err_str_json_nat.

Definition err_str_json_unrecognized_constructor := "Unrecognized constructor in JSON".
Opaque err_str_json_unrecognized_constructor.

Definition err_str_json_no_constructor_name_string := "JSON: No constructor name found in JSON".
Opaque err_str_json_no_constructor_name_string.

Close Scope string_scope.