open OUnit2
open Enigma

let index_test name input expected =
  name >:: fun _ ->
    assert_equal expected (index input) ~printer:string_of_int

let index_tests =
  [
    index_test "index of A is 0" 'A' 0;
    index_test "index of Z is 25" 'Z' 25;
    index_test "index of B is 1" 'B' 1;
    index_test "index of M is 12" 'M' 12;
    index_test "index of Y is 24" 'Y' 24;
  ]

let identity = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
let swap_ab = "BACDEFGHIJKLMNOPQRSTUVWXYZ"

let rotor_I = "EKMFLGDQVZNTOWYHXUSPAIBRCJ"
let rotor_II = "AJDKSIRUXBLHWTMCQGZNPYFVOE"
let rotor_III = "BDFHJLCPRTXVZNYEIWGAKMUSQO"

let map_r_to_l_test name wiring top_letter input expected =
  name >:: fun _ ->
    assert_equal expected
      (map_r_to_l wiring top_letter input)
      ~printer:string_of_int

let map_r_to_l_tests =
  [
    map_r_to_l_test "identity wiring at A maps 0 to 0" identity 'A' 0 0;
    map_r_to_l_test "identity wiring at A maps 25 to 25" identity 'A' 25 25;
    map_r_to_l_test "identity wiring at M maps 7 to 7" identity 'M' 7 7;
    map_r_to_l_test "swap AB at A maps 0 to 1" swap_ab 'A' 0 1;
    map_r_to_l_test "swap AB at A maps 1 to 0" swap_ab 'A' 1 0;
    map_r_to_l_test "swap AB at B maps 0 to 25" swap_ab 'B' 0 25;
    map_r_to_l_test "swap AB at B maps 25 to 0" swap_ab 'B' 25 0;
    map_r_to_l_test "swap AB at C maps 24 to 25" swap_ab 'C' 24 25;
    map_r_to_l_test "rotor I at A maps 0 to 4" rotor_I 'A' 0 4;
    map_r_to_l_test "rotor I at B maps 0 to 9" rotor_I 'B' 0 9;
    map_r_to_l_test "rotor III at O maps 14 to 17" rotor_III 'O' 14 17;
  ]

let map_l_to_r_test name wiring top_letter input expected =
  name >:: fun _ ->
    assert_equal expected
      (map_l_to_r wiring top_letter input)
      ~printer:string_of_int

let all_positions = List.init 26 Fun.id
let all_letters = List.init 26 (fun i -> Char.chr (i + Char.code 'A'))

let round_trip_test name wiring =
  name >:: fun _ ->
    List.iter
      (fun top_letter ->
        List.iter
          (fun pos ->
            assert_equal pos
              (map_l_to_r wiring top_letter (map_r_to_l wiring top_letter pos))
              ~printer:string_of_int)
          all_positions)
      all_letters

let map_l_to_r_tests =
  [
    map_l_to_r_test "identity wiring at A maps 0 to 0" identity 'A' 0 0;
    map_l_to_r_test "identity wiring at M maps 7 to 7" identity 'M' 7 7;
    map_l_to_r_test "swap AB at A maps 0 to 1" swap_ab 'A' 0 1;
    map_l_to_r_test "swap AB at B maps 0 to 25" swap_ab 'B' 0 25;
    map_l_to_r_test "swap AB at C maps 25 to 24" swap_ab 'C' 25 24;
    map_l_to_r_test "rotor I at A maps 0 to 20" rotor_I 'A' 0 20;
    map_l_to_r_test "rotor I at F maps 10 to 14" rotor_I 'F' 10 14;
    round_trip_test "rotor I l_to_r undoes r_to_l" rotor_I;
    round_trip_test "rotor III l_to_r undoes r_to_l" rotor_III;
  ]

let refl_B = "YRUHQSLDPXNGOKMIEBFZCWVJAT"
let refl_C = "FVPJIAOYEDRZXWGCTKUQSBNMHL"

let map_refl_test name wiring input expected =
  name >:: fun _ ->
    assert_equal expected (map_refl wiring input) ~printer:string_of_int

let symmetry_test name wiring =
  name >:: fun _ ->
    List.iter
      (fun pos ->
        assert_equal pos
          (map_refl wiring (map_refl wiring pos))
          ~printer:string_of_int)
      all_positions

let map_refl_tests =
  [
    map_refl_test "identity reflector maps 0 to 0" identity 0 0;
    map_refl_test "identity reflector maps 1 to 1" identity 1 1;
    map_refl_test "identity reflector maps 25 to 25" identity 25 25;
    map_refl_test "reflector B maps 0 to 24" refl_B 0 24;
    map_refl_test "reflector B maps 24 to 0" refl_B 24 0;
    map_refl_test "reflector B maps 1 to 17" refl_B 1 17;
    map_refl_test "reflector C maps 0 to 5" refl_C 0 5;
    symmetry_test "reflector B is symmetric" refl_B;
    symmetry_test "reflector C is symmetric" refl_C;
  ]

let map_plug_test name plugs input expected =
  name >:: fun _ ->
    assert_equal expected (map_plug plugs input) ~printer:(String.make 1)

let plugs_az = [ ('A', 'Z') ]
let plugs_az_xy = [ ('A', 'Z'); ('X', 'Y') ]
let plugs_yx_za = [ ('Y', 'X'); ('Z', 'A') ]

let map_plug_tests =
  [
    map_plug_test "empty plugboard leaves M unchanged" [] 'M' 'M';
    map_plug_test "empty plugboard leaves A unchanged" [] 'A' 'A';
    map_plug_test "plugboard AZ maps A to Z" plugs_az 'A' 'Z';
    map_plug_test "plugboard AZ maps Z to A" plugs_az 'Z' 'A';
    map_plug_test "plugboard AZ leaves B unchanged" plugs_az 'B' 'B';
    map_plug_test "plugboard AZ XY maps A to Z" plugs_az_xy 'A' 'Z';
    map_plug_test "plugboard AZ XY maps Z to A" plugs_az_xy 'Z' 'A';
    map_plug_test "plugboard AZ XY maps X to Y" plugs_az_xy 'X' 'Y';
    map_plug_test "plugboard AZ XY maps Y to X" plugs_az_xy 'Y' 'X';
    map_plug_test "plugboard AZ XY leaves M unchanged" plugs_az_xy 'M' 'M';
    map_plug_test "reordered plugboard YX ZA maps A to Z" plugs_yx_za 'A' 'Z';
    map_plug_test "reordered plugboard YX ZA maps X to Y" plugs_yx_za 'X' 'Y';
  ]

let historical_I = { wiring = rotor_I; turnover = 'Q' }
let historical_II = { wiring = rotor_II; turnover = 'E' }
let historical_III = { wiring = rotor_III; turnover = 'V' }
let historical_I_II_III = [ historical_I; historical_II; historical_III ]

let make_config refl rotors top_letters plugboard =
  {
    refl;
    rotors =
      List.mapi
        (fun i rotor -> { rotor; top_letter = top_letters.[i] })
        rotors;
    plugboard;
  }

let cipher_char_test name config input expected =
  name >:: fun _ ->
    assert_equal expected (cipher_char config input) ~printer:(String.make 1)

let alphabet = identity
let cipher_alphabet_test name config expected =
  name >:: fun _ ->
    assert_equal expected
      (String.map (cipher_char config) alphabet)
      ~printer:Fun.id

let identity_machine = make_config identity [] "" []
let machine_AAA = make_config refl_B historical_I_II_III "AAA" []
let machine_AAA_az = make_config refl_B historical_I_II_III "AAA" plugs_az

let cipher_char_tests =
  [
    cipher_char_test "identity machine maps A to A" identity_machine 'A' 'A';
    cipher_char_test "identity machine maps Z to Z" identity_machine 'Z' 'Z';
    cipher_alphabet_test "identity machine maps every letter to itself" identity_machine alphabet;
    cipher_char_test "reflector B alone maps A to Y" (make_config refl_B [] "" []) 'A' 'Y';
    cipher_char_test "reflector B with plugboard AB maps A to R" (make_config refl_B [] "" [ ('A', 'B') ]) 'A' 'R';
    cipher_char_test "single rotor I at A maps A to H" (make_config refl_B [ historical_I ] "A" []) 'A' 'H';
    cipher_char_test "single rotor I at B maps A to N" (make_config refl_B [ historical_I ] "B" []) 'A' 'N';
    cipher_char_test "rotors I II III at AAA map G to P" machine_AAA 'G' 'P';
    cipher_char_test "rotors I II III at AAA map P to G" machine_AAA 'P' 'G';
    cipher_char_test "rotors I II III at AAA map A to U" machine_AAA 'A' 'U';
    cipher_char_test "rotors I II III at AAA map Z to H" machine_AAA 'Z' 'H';
    cipher_alphabet_test "rotors I II III at AAA full mapping" machine_AAA "UEJOBTPZWCNSRKDGVMLFAQIYXH";
    cipher_char_test "plugboard AZ at AAA maps A to H" machine_AAA_az 'A' 'H';
    cipher_char_test "plugboard AZ at AAA maps U to Z" machine_AAA_az 'U' 'Z';
    cipher_alphabet_test "plugboard AZ at AAA full mapping" machine_AAA_az "HEJOBTPAWCNSRKDGVMLFZQIYXU";
    cipher_char_test "rotors III II I at KDO, reflector C, plugboard AZ XY" (make_config refl_C [ historical_III; historical_II; historical_I ] "KDO" plugs_az_xy) 'H' 'R';
  ]

let historical_III_II_I = [ historical_III; historical_II; historical_I ]

let top_letters config =
  config.rotors
  |> List.map (fun { top_letter; _ } -> String.make 1 top_letter)
  |> String.concat ""

let step_test name rotors before after =
  name >:: fun _ ->
    assert_equal after
      (make_config refl_B rotors before [] |> step |> top_letters)
      ~printer:Fun.id

(* Rule 1: the rightmost rotor always steps once before each character. *)
let step_rule_1_tests =
  [
    step_test "rightmost rotor steps every character" historical_III_II_I "AAA" "AAB";
    step_test "rightmost rotor wraps from Z to A" historical_III_II_I "AAZ" "AAA";
    step_test "single rotor steps from A to B" [ historical_I ] "A" "B";
    step_test "single rotor wraps from Z to A" [ historical_I ] "Z" "A";
    step_test "stepping KDO gives KDP" historical_III_II_I "KDO" "KDP";
    step_test "machine with no rotors is unchanged" [] "" "";
    ( "step keeps the reflector, plugboard and rotor wirings" >:: fun _ ->
      let config =
        make_config refl_C historical_III_II_I "KDO" plugs_az_xy
      in
      let stepped = step config in
      assert_equal config.refl stepped.refl;
      assert_equal config.plugboard stepped.plugboard;
      assert_equal
        (List.map (fun { rotor; _ } -> rotor) config.rotors)
        (List.map (fun { rotor; _ } -> rotor) stepped.rotors) );
  ]

let step_sequence_test name rotors expected =
  name >:: fun _ ->
    match expected with
    | [] -> failwith "step_sequence_test requires a starting position"
    | start :: _ ->
        let rec steps config n =
          if n = 0 then []
          else
            let config = step config in
            top_letters config :: steps config (n - 1)
        in
        let config = make_config refl_B rotors start [] in
        assert_equal expected
          (start :: steps config (List.length expected - 1))
          ~printer:(String.concat " ")

(* Rule 2: a rotor other than the leftmost that shows its own turnover
   letter steps, and so does the rotor immediately to its left. *)
let step_rule_2_tests =
  [
    step_test "rightmost at turnover KDQ steps middle to KER" historical_III_II_I "KDQ" "KER";
    step_test "middle at turnover KER steps itself and left to LFS" historical_III_II_I "KER" "LFS";
    step_test "after the double step LFS gives LFT" historical_III_II_I "LFS" "LFT";
    step_test "rightmost at turnover VDQ steps middle to VER" historical_III_II_I "VDQ" "VER";
    step_test "middle at turnover VER steps itself and left to WFS" historical_III_II_I "VER" "WFS";
    step_test "middle at turnover alone AEA steps to BFB" historical_III_II_I "AEA" "BFB";
    step_test "leftmost at its turnover VAA does not step" historical_III_II_I "VAA" "VAB";
    step_test "two rotors, rightmost at turnover AQ gives BR" [ historical_II; historical_I ] "AQ" "BR";
    step_test "two rotors, leftmost at turnover EA gives EB" [ historical_II; historical_I ] "EA" "EB";
    step_sequence_test "stepping sequence from KDO" historical_III_II_I [ "KDO"; "KDP"; "KDQ"; "KER"; "LFS"; "LFT"; "LFU" ];
    step_sequence_test "stepping sequence from VDP" historical_III_II_I [ "VDP"; "VDQ"; "VER"; "WFS"; "WFT" ];
  ]

(* Rule 3: no rotor steps more than once per character, even when several
   rules apply to it. *)
let step_rule_3_tests =
  [
    step_test "middle at turnover and pushed by right steps once to BFR" historical_III_II_I "AEQ" "BFR";
    step_test "single rotor at its turnover steps once" [ historical_I ] "Q" "R";
    step_test "two rotors both at turnover EQ give FR" [ historical_II; historical_I ] "EQ" "FR";
    step_test "four rotors all pushed step once each to BWFR" [ historical_I; historical_III; historical_II; historical_I ] "AVEQ" "BWFR";
  ]

let cipher_test name config input expected =
  name >:: fun _ -> assert_equal expected (cipher config input) ~printer:Fun.id

let decipher_test name config plaintext =
  name >:: fun _ ->
    assert_equal plaintext
      (plaintext |> cipher config |> cipher config)
      ~printer:Fun.id

let machine_FUN_az = make_config refl_B historical_I_II_III "FUN" plugs_az
let machine_KDO = make_config refl_C historical_III_II_I "KDO" plugs_az_xy

let cipher_tests =
  [
    cipher_test "empty string enciphers to empty string" machine_AAA "" "";
    cipher_test "cipher steps before enciphering G at AAA" machine_AAA "G" "X";
    cipher_test "AAAAA at AAA enciphers to BDZGO" machine_AAA "AAAAA" "BDZGO";
    cipher_test "YNGXQ at FUN with plugboard AZ is OCAML" machine_FUN_az "YNGXQ" "OCAML";
    cipher_test "OCAML at FUN with plugboard AZ is YNGXQ" machine_FUN_az "OCAML" "YNGXQ";
    cipher_test "machine with no rotors enciphers ABC to YRU" (make_config refl_B [] "" [])"ABC" "YRU";
    cipher_test "HELLOWORLD from KDO through a double step" machine_KDO "HELLOWORLD" "RAFFYYYNZY";
    decipher_test "deciphering HELLO at FUN recovers it" machine_FUN_az "HELLO";
    decipher_test "deciphering HELLO from KDO recovers it" machine_KDO "HELLO";
  ]

let qwerty_rotor = { wiring = "QWERTYUIOPASDFGHJKLZXCVBNM"; turnover = 'C' }

let full_plugboard =
  List.init 13 (fun i ->
      (Char.chr (Char.code 'A' + (2 * i)), Char.chr (Char.code 'B' + (2 * i))))

let long_text =
  List.init 30 (fun _ -> "THEQUICKBROWNFOXJUMPSOVERTHELAZYDOG")
  |> String.concat ""

let machine_MCK_full = make_config refl_B historical_I_II_III "MCK" full_plugboard

let whole_machine_tests =
  [
    cipher_test "single rotor wraps from Z while enciphering" (make_config refl_B [ historical_I ] "Z" []) "ABC" "HOH";
    cipher_test "four rotors including a non-historical one" (make_config refl_B [ historical_I; qwerty_rotor; historical_II; historical_III ] "ABEU" []) "ENIGMA" "DOMBOK";
    cipher_test "non-historical turnover C steps the left rotor" (make_config refl_C [ qwerty_rotor; qwerty_rotor ] "AB" []) "CCCC" "LLJF";
    cipher_test "full plugboard with all 13 cables" machine_MCK_full "FUNCTIONAL" "RPGDMCBBLR";
    cipher_test "rotors II III I at XYZ, reflector C, plugboard AZ XY" (make_config refl_C [ historical_II; historical_III; historical_I ] "XYZ" plugs_az_xy) "PROGRAMMING" "GYQQMXSCQOJ";
    decipher_test "deciphering a long message recovers it" machine_MCK_full long_text;
    ( "no letter ever enciphers to itself" >:: fun _ ->
      let ciphertext = cipher machine_MCK_full long_text in
      String.iteri
        (fun i c ->
          assert_bool
            (Printf.sprintf "letter %d enciphered to itself" i)
            (c <> long_text.[i]))
        ciphertext );
    ( "order of plugboard pairs does not change the ciphertext" >:: fun _ ->
      let with_plugs plugs =
        cipher (make_config refl_B historical_I_II_III "KDO" plugs) long_text
      in
      assert_equal (with_plugs plugs_az_xy) (with_plugs plugs_yx_za)
        ~printer:Fun.id );
    ( "cipher of one letter is cipher_char after one step" >:: fun _ ->
      assert_equal
        (String.make 1 (cipher_char (step machine_KDO) 'H'))
        (cipher machine_KDO "H") ~printer:Fun.id );
  ]

let suite =
  "Enigma test suite"
  >::: List.flatten
         [
           index_tests;
           map_r_to_l_tests;
           map_l_to_r_tests;
           map_refl_tests;
           map_plug_tests;
           cipher_char_tests;
           step_rule_1_tests;
           step_rule_2_tests;
           step_rule_3_tests;
           cipher_tests;
           whole_machine_tests;
         ]
let () = run_test_tt_main suite
