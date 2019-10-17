
module InlineOrderCfuns (reorder_cfuns) where

import Prelude hiding (filter,map)
import List

import Names
import InlineMatch
import ProgramDef
import Skeleton
import BodyTypeDefs

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
        err_msg = "The signature of a local cfun seems to be missing"
        (b,bs') = find' err_msg (p a) bs
     in ((a, b) : r)

contains_no_local_cfun_call_bod :: QName -> Coq_cfun_bod_named -> Bool
contains_no_local_cfun_call_bod qn bod =
    all (contains_no_local_cfun_call_b qn . snd) (snd bod)

reorder_inline :: [(Coq_cfun_bod_named, Coq_cfun_sig)] -> [(Coq_cfun_bod_named, Coq_cfun_sig)]
reorder_inline l = go (ascribe (zip (repeat []) l) (fmap (fst . fst) l)) []
    where
        ascribe :: [([QName], (Coq_cfun_bod_named, Coq_cfun_sig))] -> [QName] -> [([QName], (Coq_cfun_bod_named, Coq_cfun_sig))]
        ascribe [] _ = []
        ascribe l [] = l
        ascribe l (q:qs) = let l' = fmap (\(ls, (bod, sig)) ->
                                            let ls' = if contains_no_local_cfun_call_bod q bod
                                                      then ls
                                                      else (q:ls)
                                             in (ls', (bod, sig)))
                                             l
                           in ascribe l' qs
        go [] xs = xs
        go ls xs = let err_msg      = "Cfuns cannot be ordered for inlining"
                       (next, rest) = find' err_msg ((== []) . fst) ls
                       rest'        = fmap (\(qs, x) -> (filter (/= (fst (fst (snd next)))) qs, x)) rest
                    in go rest' (snd next : xs)



reorder_cfuns :: Coq_program -> Coq_program
reorder_cfuns p =
    case program_cfun_bods_g p of
      [] -> p
      (cfun : _) ->
            Coq_mkProgram
                reordered_skeleton
                (program_fun_bods p)
                (program_cfun_bods_g p)
                reordered_cfuns
                (program_gfun_bods_g p)
                (program_gfun_bods_l p)
                where
                skeleton_old = (program_skeleton p)
                cfuns_old = (program_cfun_bods_l p)
                sigs_old = (skeleton_cfun_sigs_l skeleton_old)
                sorted_all = sort_with (\bod sig -> fst bod == fst (fst sig)) cfuns_old sigs_old
                reordered_all = reorder_inline sorted_all
                reordered_skeleton =
                    (Coq_mkSkeleton
                        (skeleton_dts skeleton_old)
                        (skeleton_ctors skeleton_old)
                        (skeleton_cdts skeleton_old)
                        (skeleton_dtors skeleton_old)
                        (skeleton_fun_sigs skeleton_old)
                        (skeleton_cfun_sigs_g skeleton_old)
                        (fmap snd reordered_all)
                        (skeleton_gfun_sigs_g skeleton_old)
                        (skeleton_gfun_sigs_l skeleton_old))
                reordered_cfuns = fmap fst reordered_all

