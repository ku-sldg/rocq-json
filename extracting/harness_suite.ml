module J = Jsonifiable_suite

let b v = if v then J.True else J.False

let ascii_of_char c =
  let n = Char.code c in
  J.Ascii
    ( b (n land 1 <> 0),
      b (n land 2 <> 0),
      b (n land 4 <> 0),
      b (n land 8 <> 0),
      b (n land 16 <> 0),
      b (n land 32 <> 0),
      b (n land 64 <> 0),
      b (n land 128 <> 0) )

let rec string_of_ocaml s i =
  if i = String.length s then J.EmptyString
  else J.String (ascii_of_char s.[i], string_of_ocaml s (i + 1))

let js s = string_of_ocaml s 0

let rec nat_of_int n =
  if n <= 0 then J.O else J.S (nat_of_int (n - 1))

let nat_jsonifiable =
  {
    J.to_JSON = (fun n -> J.JSON_Nat n);
    from_JSON =
      (function
      | J.JSON_Nat n -> J.Res n
      | _ -> J.Err (js "expected nat"));
  }

let string_jsonifiable =
  {
    J.to_JSON = (fun s -> J.JSON_String s);
    from_JSON =
      (function
      | J.JSON_String s -> J.Res s
      | _ -> J.Err (js "expected string"));
  }

let bool_jsonifiable =
  {
    J.to_JSON = (fun v -> J.JSON_Boolean v);
    from_JSON =
      (function
      | J.JSON_Boolean v -> J.Res v
      | _ -> J.Err (js "expected bool"));
  }

let enum_values =
  [
    J.E00; J.E01; J.E02; J.E03; J.E04; J.E05; J.E06; J.E07;
    J.E08; J.E09; J.E0A; J.E0B; J.E0C; J.E0D; J.E0E; J.E0F;
    J.E10; J.E11; J.E12; J.E13; J.E14; J.E15; J.E16; J.E17;
    J.E18; J.E19; J.E1A; J.E1B; J.E1C; J.E1D; J.E1E; J.E1F;
    J.E20; J.E21; J.E22; J.E23; J.E24; J.E25; J.E26; J.E27;
    J.E28; J.E29; J.E2A; J.E2B; J.E2C; J.E2D; J.E2E; J.E2F;
    J.E30; J.E31; J.E32; J.E33; J.E34; J.E35; J.E36; J.E37;
    J.E38; J.E39; J.E3A; J.E3B; J.E3C; J.E3D; J.E3E; J.E3F;
    J.E40; J.E41; J.E42; J.E43; J.E44; J.E45; J.E46; J.E47;
    J.E48; J.E49; J.E4A; J.E4B; J.E4C; J.E4D; J.E4E; J.E4F;
    J.E50; J.E51; J.E52; J.E53; J.E54; J.E55; J.E56; J.E57;
    J.E58; J.E59; J.E5A; J.E5B; J.E5C; J.E5D; J.E5E; J.E5F;
    J.E60; J.E61; J.E62; J.E63; J.E64; J.E65; J.E66; J.E67;
    J.E68; J.E69; J.E6A; J.E6B; J.E6C; J.E6D; J.E6E; J.E6F;
    J.E70; J.E71; J.E72; J.E73; J.E74; J.E75; J.E76; J.E77;
    J.E78; J.E79; J.E7A; J.E7B; J.E7C; J.E7D; J.E7E; J.E7F;
    J.E80; J.E81; J.E82; J.E83; J.E84; J.E85; J.E86; J.E87;
    J.E88; J.E89; J.E8A; J.E8B; J.E8C; J.E8D; J.E8E; J.E8F;
    J.E90; J.E91; J.E92; J.E93; J.E94; J.E95; J.E96; J.E97;
    J.E98; J.E99; J.E9A; J.E9B; J.E9C; J.E9D; J.E9E; J.E9F;
    J.EA0; J.EA1; J.EA2; J.EA3; J.EA4; J.EA5; J.EA6; J.EA7;
    J.EA8; J.EA9; J.EAA; J.EAB; J.EAC; J.EAD; J.EAE; J.EAF;
    J.EB0; J.EB1; J.EB2; J.EB3; J.EB4; J.EB5; J.EB6; J.EB7;
    J.EB8; J.EB9; J.EBA; J.EBB; J.EBC; J.EBD; J.EBE; J.EBF;
    J.EC0; J.EC1; J.EC2; J.EC3; J.EC4; J.EC5; J.EC6; J.EC7;
    J.EC8; J.EC9; J.ECA; J.ECB; J.ECC; J.ECD; J.ECE; J.ECF;
    J.ED0; J.ED1; J.ED2; J.ED3; J.ED4; J.ED5; J.ED6; J.ED7;
    J.ED8; J.ED9; J.EDA; J.EDB; J.EDC; J.EDD; J.EDE; J.EDF;
    J.EE0; J.EE1; J.EE2; J.EE3; J.EE4; J.EE5; J.EE6; J.EE7;
    J.EE8; J.EE9; J.EEA; J.EEB; J.EEC; J.EED; J.EEE; J.EEF;
    J.EF0; J.EF1; J.EF2; J.EF3; J.EF4; J.EF5; J.EF6; J.EF7;
    J.EF8; J.EF9; J.EFA; J.EFB; J.EFC; J.EFD; J.EFE; J.EFF;
  ]

let point_values =
  [ J.MkPoint2D (nat_of_int 1, nat_of_int 2); J.MkPoint2D (nat_of_int 13, nat_of_int 21) ]

let role_values =
  [
    J.Admin;
    J.Moderator (nat_of_int 2);
    J.StandardUser (nat_of_int 7, js "alice");
    J.Guest;
  ]

let server_config_values =
  [
    { J.host = js "localhost"; port = nat_of_int 8080; use_ssl = J.False };
    { J.host = js "example.org"; port = nat_of_int 443; use_ssl = J.True };
  ]

let instruction_values =
  [
    J.INop;
    J.IPush (nat_of_int 1);
    J.IPop;
    J.ILoad (nat_of_int 2);
    J.IStore (nat_of_int 3);
    J.IHalt;
  ]

let tree_values =
  [
    J.BinLeaf;
    J.BinNode (J.BinLeaf, nat_of_int 1, J.BinLeaf);
    J.BinNode
      ( J.BinNode (J.BinLeaf, nat_of_int 2, J.BinLeaf),
        nat_of_int 3,
        J.BinNode (J.BinLeaf, nat_of_int 4, J.BinLeaf) );
  ]

let bench csv run iterations name f =
  let start = Sys.time () in
  for _ = 1 to iterations do
    f ()
  done;
  let elapsed = Sys.time () -. start in
  Printf.printf "BENCH %s %.6f\n%!" name elapsed;
  Printf.fprintf csv "%s,%d,%.6f\n%!" name run elapsed

let roundtrip to_json from_json values () =
  List.iter
    (fun v ->
      let result = from_json (to_json v) in
      ignore (Sys.opaque_identity result))
    values

let () =
  let runs = try int_of_string (Sys.getenv "JSONIFIABLE_EXTRACTION_RUNS") with _ -> 10 in
  let iterations = try int_of_string (Sys.getenv "JSONIFIABLE_SUITE_ITERS") with _ -> 20_000 in
  let csv = open_out "extraction_bench.csv" in
  let generated_enum = J.enum_256_Jsonifiable in
  let handwritten_enum = J.enum_256_Jsonifiable' in
  let generated_point = J.point2D_Jsonifiable nat_jsonifiable in
  let generated_role = J.userRole_Jsonifiable nat_jsonifiable string_jsonifiable in
  let generated_server_config = J.serverConfig_Jsonifiable string_jsonifiable nat_jsonifiable bool_jsonifiable in
  let generated_instruction = J.instruction_Jsonifiable nat_jsonifiable in
  let generated_tree = J.binTree_Jsonifiable nat_jsonifiable in
  let handwritten_point = J.point2D_Jsonifiable' nat_jsonifiable in
  let handwritten_role = J.userRole_Jsonifiable' nat_jsonifiable string_jsonifiable in
  let handwritten_server_config = J.serverConfig_Jsonifiable' string_jsonifiable nat_jsonifiable bool_jsonifiable in
  let handwritten_instruction = J.instruction_Jsonifiable' nat_jsonifiable in
  let handwritten_tree = J.binTree_Jsonifiable' nat_jsonifiable in
  Printf.fprintf csv "benchmark,run,seconds\n";
  for run = 1 to runs do
    Printf.printf "Running harness_suite.exe... run %d/%d\n%!" run runs;
    bench csv run iterations "enum256_generated" (roundtrip generated_enum.J.to_JSON generated_enum.J.from_JSON enum_values);
    bench csv run iterations "enum256_handwritten" (roundtrip handwritten_enum.J.to_JSON handwritten_enum.J.from_JSON enum_values);
    bench csv run iterations "point2d_generated" (roundtrip generated_point.J.to_JSON generated_point.J.from_JSON point_values);
    bench csv run iterations "point2d_handwritten" (roundtrip handwritten_point.J.to_JSON handwritten_point.J.from_JSON point_values);
    bench csv run iterations "userrole_generated" (roundtrip generated_role.J.to_JSON generated_role.J.from_JSON role_values);
    bench csv run iterations "userrole_handwritten" (roundtrip handwritten_role.J.to_JSON handwritten_role.J.from_JSON role_values);
    bench csv run iterations "serverconfig_generated"
      (roundtrip generated_server_config.J.to_JSON generated_server_config.J.from_JSON server_config_values);
    bench csv run iterations "serverconfig_handwritten"
      (roundtrip handwritten_server_config.J.to_JSON handwritten_server_config.J.from_JSON server_config_values);
    bench csv run iterations "instruction_generated"
      (roundtrip generated_instruction.J.to_JSON generated_instruction.J.from_JSON instruction_values);
    bench csv run iterations "instruction_handwritten"
      (roundtrip handwritten_instruction.J.to_JSON handwritten_instruction.J.from_JSON instruction_values);
    bench csv run iterations "bintree_generated" (roundtrip generated_tree.J.to_JSON generated_tree.J.from_JSON tree_values);
    bench csv run iterations "bintree_handwritten" (roundtrip handwritten_tree.J.to_JSON handwritten_tree.J.from_JSON tree_values)
  done;
  close_out csv;
  close_out (open_out "benched.stamp")
