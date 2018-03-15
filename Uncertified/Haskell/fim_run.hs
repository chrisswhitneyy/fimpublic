module Main where

import Text.Printf
import Control.Exception
import System.CPUTime
import Control.Monad
import System.Environment
import Datatypes

import qualified SeqFIM
import qualified PerfFIM

import DataZoo
#ifdef NATIVE
import DataMushroom
import DataRetail1000
import DataRetail2000
#endif /* NATIVE */


#ifndef NATIVE
import BinNums

instance Show Coq_positive where
  show (Coq_xI p) = (show p)++"1"
  show (Coq_xO p) = (show p)++"0"
  show Coq_xH = "1"

instance Show Z where
  show Z0 = "0"
  show (Zpos p) = show p
  show (Zneg p) = "-"++(show p)
#endif /* NATIVE */

#ifdef NATIVE
-- Specification from Hu et al., PADL 2000
fs least vss os = filter (fsp vss least) (subs os)

fsp vss least ys = Datatypes.length (filter (ys `isSublist`) vss) >= least

[] `isSublist` ys = True
(x:xs) `isSublist` ys = (x `isEle` ys) && (xs `isSublist` ys)

e `isEle` [] = False
e `isEle` (x:xs) = if e==x then True else e `isEle` xs

subs [] = [[]]
subs (x:xs) = subs xs ++ map (x:) (subs xs)

-- Calculated version from Hu et al., PADL 2000
data Tree a = Node a [Tree a]

fso least vss os = tab os least (Node ([],vss) [])

tab [] least t = select least t
tab (o:os) least t = tab os least (add o least t)

select least (Node (r,vss) []) = [r]
select least (Node (r,vss) ts) = r : foldr (++) [] (map (select least) ts)

add o least (t@(Node (r,vss) [])) =
  let vss' = filter (o `isEle'`) vss in
  if Datatypes.length vss' >= least
  then Node (r,vss) [Node (r++[o], vss') []]
  else t
add o least (t@(Node (r,vss) ts)) =
  let vss' = filter (o `isEle'`) vss
  in  if Datatypes.length vss' >= least
      then Node (r,vss)
           (Node (r++[o], vss') [] : map (add o least) ts)
      else t

fsc least vss os = tab' os least (Node ([],vss) [])

tab' [] least t = select least t
tab' (o:os) least t = tab' os least (add' o least t)

add' o least (t@(Node (r,vss) [])) =
  let vss' = filter (o `isEle`) vss in
  if Datatypes.length vss' >= least
  then Node (r,vss) [Node (r++[o], vss') []]
  else t
add' o least (t@(Node (r,vss) ts)) =
  let vss' = filter (o `isEle`) vss
  in  if Datatypes.length vss' >= least
      then Node (r,vss)
           (Node (r++[o], vss') [] : map (add o least) ts)
      else t

e `isEle'` [] = False
e `isEle'` (x:xs) = if e<x then False
                    else (if e==x then True else e `isEle'` xs)
#endif

-- Selection of versions

select_vss 0 = DataZoo.vss
#ifdef NATIVE
select_vss 1 = DataMushroom.vss
select_vss 2 = DataRetail1000.vss
select_vss 3 = DataRetail2000.vss
#endif /* NATIVE */

select_os 0 = DataZoo.os
#ifdef NATIVE
select_os 1 = DataMushroom.os
select_os 2 = DataRetail1000.os
select_os 3 = DataRetail2000.os
#endif /* NATIVE */
  
select_least 0 = DataZoo.least
#ifdef NATIVE
select_least 1 = DataMushroom.least
select_least 2 = DataRetail1000.least
select_least 3 = DataRetail2000.least
#endif /* NATIVE */

select_fim 0 = SeqFIM.fim
select_fim 1 = SeqFIM.fim1
select_fim 2 = \least vss os -> SeqFIM.fim2 least vss [] os
select_fim 3 = \least vss os -> SeqFIM.at_least least vss
                                (SeqFIM.fim3 least vss [] os)
select_fim 4 = SeqFIM.fim4
select_fim 5 = SeqFIM.fim5
select_fim 6 = PerfFIM.fim6
#ifdef NATIVE
select_fim 7 = fs
select_fim 8 = fsc
select_fim 9 = fso
#endif


string_data 0 = "Zoo"
string_data 1 = "Mushroom"
string_data 2 = "Retail1000"
string_data 3 = "Retail2000"

string_fim 0 = "Coq extraction: SeqFIM.fim"
string_fim 1 = "Coq extraction: SeqFIM.fim1"
string_fim 2 = "Coq extraction: least vss os -> fim2 least vss [] os"
string_fim 3 = "Coq extraction: least vss os -> at_least least vss (fim3 least vss [] os)"
string_fim 4 = "Coq extraction: SeqFIM.fim4"
string_fim 5 = "Coq extraction: SeqFIM.fim5"
string_fim 6 = "Coq extraction: PerfFIM.fim6"
#ifdef NATIVE
string_fim 7 = "Hu et al., PADL 2000: specification"
string_fim 8 = "Hu et al., PADL 2000: calculated version"
string_fim 9 = "Hu et al., PADL 2000: calculated version + sorted list optimization"
#endif

main = do
  [set, v] <- getArgs
  let dataset = (read set)::Int
      version = (read v)::Int
      vss = select_vss dataset
      os  = select_os dataset
      least = select_least dataset
      fim = select_fim version
  printf "set: %s\nversion: %s\n" (string_data dataset) (string_fim version)
  start <- getCPUTime
  printf "length of result: %d\n" (Prelude.length(fim least vss os))
  end <- getCPUTime
  let diff = (fromIntegral (end - start)) / (10^12)
  printf "Computation time: %0.9f sec\n" (diff :: Double)
