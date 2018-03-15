let usage () = 
  begin
    print_string ("Usage: "^(Sys.argv.(0))^" dataset fim_version\n"
                  ^"  datasets:\n\t0 - Zoo\n\t1 - Mushroom\n\t"
                  ^"2 - Retail1000\n\tRetail2000\n"
                  ^"  versions: 0 to 6\n");
    exit 1;
  end
        
let dataset =
  try
    int_of_string (Sys.argv.(1))
  with _ -> usage ()

let version =
  try
    int_of_string (Sys.argv.(2))
  with _ -> usage ()

let start_time = ref 0.
let end_time = ref 0.

module type DATA =
sig
  type size
  type item
  val least : size
  val os : item list
  val vss: item list list
end

let select dataset version =
  let fim = 
    match version with
    | 0 -> SeqFIM.fim
    | 1 -> SeqFIM.fim1
    | 2 -> fun least vss os -> SeqFIM.fim2 least vss [] os
    | 3 -> fun least vss os ->
      SeqFIM.at_least least vss (SeqFIM.fim3 least vss [] os)
    | 4 -> SeqFIM.fim4
    | 5 -> SeqFIM.fim5
    | 6 -> PerfFIM.fim6 
    | _ -> usage () in
  let (least,os,vss) = 
    match dataset with
    | 0 -> DataZoo.least, DataZoo.os, DataZoo.vss
    | 1 -> DataMushroom.least, DataMushroom.os, DataMushroom.vss
    | 2 -> DataRetail1000.least, DataRetail1000.os, DataRetail1000.vss
    | 3 -> DataRetail2000.least, DataRetail2000.os, DataRetail2000.vss
    | _ -> usage () in
  fim least vss os

let conv n =
#ifdef BIGINT
  Big.to_int n
#endif
#ifdef NAT
  let rec to_int =
    function Datatypes.O -> 0
           | Datatypes.S n -> 1+(to_int n) in
  to_int n
#endif
#ifndef BIGINT
#ifndef NAT
  n
#endif
#endif

let string_data = function
    0 -> "Zoo"
  | 1 -> "Mushroom"
  | 2 -> "Retail1000"
  | 3 -> "Retail2000"
  | _ -> usage()

let string_fim = function
  | 0 -> "Coq extraction: SeqFIM.fim"
  | 1 -> "Coq extraction: SeqFIM.fim1"
  | 2 -> "Coq extraction: least vss os -> fim2 least vss [] os"
  | 3 -> "Coq extraction: least vss os -> at_least least vss (fim3 least vss [] os)"
  | 4 -> "Coq extraction: SeqFIM.fim4"
  | 5 -> "Coq extraction: SeqFIM.fim5"
  | 6 -> "Coq extraction: PerfFIM.fim6"
  | _ -> usage ()
    

let _ =
  begin
    Printf.printf "set: %s\nversion: %s\n"
      (string_data dataset) (string_fim version);
    start_time := Unix.gettimeofday ();
    Printf.printf "length of result: %d\n"
      (conv (Datatypes.length (select dataset version)));
    end_time := Unix.gettimeofday ();
    Printf.printf "Computation time: %f sec\n" (!end_time -. !start_time)
  end

