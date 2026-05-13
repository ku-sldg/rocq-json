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
    J.C00; J.C01; J.C02; J.C03; J.C04; J.C05; J.C06; J.C07;
    J.C08; J.C09; J.C0A; J.C0B; J.C0C; J.C0D; J.C0E; J.C0F;
    J.C10; J.C11; J.C12; J.C13; J.C14; J.C15; J.C16; J.C17;
    J.C18; J.C19; J.C1A; J.C1B; J.C1C; J.C1D; J.C1E; J.C1F;
    J.C20; J.C21; J.C22; J.C23; J.C24; J.C25; J.C26; J.C27;
    J.C28; J.C29; J.C2A; J.C2B; J.C2C; J.C2D; J.C2E; J.C2F;
    J.C30; J.C31; J.C32; J.C33; J.C34; J.C35; J.C36; J.C37;
    J.C38; J.C39; J.C3A; J.C3B; J.C3C; J.C3D; J.C3E; J.C3F;
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
  let generated_enum = J.enum_64_Jsonifiable in
  let handwritten_enum = J.enum_64_Jsonifiable' in
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
    bench csv run iterations "enum64_generated" (roundtrip generated_enum.J.to_JSON generated_enum.J.from_JSON enum_values);
    bench csv run iterations "enum64_handwritten" (roundtrip handwritten_enum.J.to_JSON handwritten_enum.J.from_JSON enum_values);
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
