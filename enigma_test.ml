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

let suite =
  "Enigma test suite"
  >::: List.flatten
         [
           index_tests;
           map_r_to_l_tests;
           map_l_to_r_tests;
           map_refl_tests;
           map_plug_tests;
         ]
let () = run_test_tt_main suite
