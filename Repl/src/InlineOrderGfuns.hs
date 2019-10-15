
module InlineOrderGfuns (reorder_gfuns) where

import Prelude hiding (filter,map)
import List
import Data.Maybe

import AST
import Names
import InlineComatch
import ProgramDef
import Skeleton
import BodyTypeDefs

import Data.Maybe
import Data.Either
import System.IO.Unsafe
import Parser.DeclarationParser
import RefuncIII
import Plumbing


find' :: String -> (a -> Bool) -> [a] -> (a, [a])
find' s _ [] = error s
find' s q (x:xs) = if q x
                   then (x, xs)
                   else let (y, ys) = find' s q xs
                       in (y, x:ys)
        
sort_with :: (a -> b -> Bool) -> [a] -> [b] -> [(a, b)]
sort_with _ [] _ = []
sort_with _ _ [] = []
sort_with p (a:as) bs = 
    let r = sort_with p as bs'
        err_msg = "The signature of a local gfun seems to be missing" 
        (b,bs') = find' err_msg (p a) bs
     in ((a, b) : r)

contains_no_local_gfun_call_bod :: QName -> Coq_gfun_bod_named -> Bool
contains_no_local_gfun_call_bod qn bod =
    all (contains_no_local_gfun_call_b qn . snd) (snd bod)

reorder_inline :: [(Coq_gfun_bod_named, Coq_gfun_sig)] -> [(Coq_gfun_bod_named, Coq_gfun_sig)]
reorder_inline l = go (ascribe (zip (repeat []) l) (fmap (fst . fst) l)) []
    where
        ascribe :: [([QName], (Coq_gfun_bod_named, Coq_gfun_sig))] -> [QName] -> [([QName], (Coq_gfun_bod_named, Coq_gfun_sig))]
        ascribe [] _ = []
        ascribe l [] = l
        ascribe l (q:qs) = let l' = fmap (\(ls, (bod, sig)) -> 
                                            let ls' = if contains_no_local_gfun_call_bod q bod
                                                      then ls
                                                      else (q:ls)
                                             in (ls', (bod, sig)))
                                             l
                           in ascribe l' qs
        go [] xs = xs
        go ls xs = let err_msg      = "Gfuns cannot be ordered for inlining"
                       (next, rest) = find' err_msg ((== []) . fst) ls
                       rest'        = fmap (\(qs, x) -> (filter (/= (fst (fst (snd next)))) qs, x)) rest
                    in go rest' (snd next : xs)



reorder_gfuns :: Coq_program -> Coq_program
reorder_gfuns p = 
    case program_gfun_bods_g p of
      [] -> p
      (gfun : _) ->
            Coq_mkProgram 
                reordered_skeleton
                (program_fun_bods p)
                (program_cfun_bods_g p)
                (program_cfun_bods_l p)
                (program_gfun_bods_g p)
                reordered_gfuns
                where 
                qn = fst gfun
                skeleton_old = (program_skeleton p)
                gfuns_old = (program_gfun_bods_l p)
                sigs_old = (skeleton_gfun_sigs_l skeleton_old)
                sorted_all = sort_with (\bod sig -> fst bod == fst sig) gfuns_old sigs_old
                reordered_all = reorder_inline sorted_all
                reordered_skeleton = 
                    (Coq_mkSkeleton
                        (skeleton_dts skeleton_old)
                        (skeleton_ctors skeleton_old)
                        (skeleton_cdts skeleton_old)
                        (skeleton_dtors skeleton_old)
                        (skeleton_fun_sigs skeleton_old)
                        (skeleton_cfun_sigs_g skeleton_old)
                        (skeleton_cfun_sigs_l skeleton_old))
                        (skeleton_gfun_sigs_g skeleton_old)
                        (fmap snd reordered_all)
                reordered_gfuns = fmap fst reordered_all



--prog :: Coq_program
--prog = flip refunctionalize_program "Stream" $ fromRight (error "parse failed") $ parseProgram  $ unsafePerformIO $ readFile "simple_nested.ub"

-- skel :: Coq_skeleton
-- skel = program_skeleton prog

-- bods :: Coq_gfun_bods
-- bods = program_gfun_bods_l prog

-- sigs :: Coq_gfun_sigs
-- sigs = skeleton_gfun_sigs_l skel

-- zipped :: [(Coq_gfun_bod_named, Coq_gfun_sig)]
-- zipped = zip bods sigs
