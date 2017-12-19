-- ---------------------------------------------------------------- [ Tree.idr ]
-- Module      : Data.Hitchhiker.Tree
-- Description : An Idris implementation of hitchhiker trees.
-- Copyright   : (c) 2016 Eric Bailey
-- License     : BSD-3
-- Link        : https://github.com/elm-community/string-extra
-- --------------------------------------------------------------------- [ EOH ]
||| Hitchhiker trees.
module Data.Hitchhiker.Tree

import public Data.Vect


-- -------------------------------------------------------------- [ Statements ]

%access public export


||| Specify a change in value `a` for a particular key `k`.
data Statement : Type -> Type -> Type where

     ||| Assert the value of `k` is `a`.
     Assert : k -> a -> Statement k a

     ||| Retract the value of `k`.
     Retract : k -> Statement k a


export
keyFor : Statement k a -> k
keyFor (Assert k _) = k
keyFor (Retract k)  = k


export
toStatement : k -> Maybe a -> Statement k a
toStatement k = maybe (Retract k) (Assert k)


export
valueFor : Statement k a -> Maybe a
valueFor (Assert _ a) = Just a
valueFor (Retract _)  = Nothing


Log : Type -> Type -> Type
Log k a = List (Statement k a)


NodeLog : Nat -> Type -> Type -> Type
NodeLog l k a = Vect l (Statement k a)


Leaves : Nat -> Type -> Type -> Type
Leaves c k a = Vect c (k, Log k a)

-- type Hitchhiker l b k = (Ord k, KnownNat l, KnownNat b, 2 ::<= b)
Hitchhiker : Ord k => (l, b, k : Nat) -> Type
Hitchhiker l b k = LTE 2 b


mutual

    Children : (c, d, l, b : Nat) -> Type -> Type -> Type
    Children c d l b k a = Vect c (k, HNode d l b k a)

    data HNode : (d, l, b : Nat) -> Type -> Type -> Type where

         HLeaf : Ord k => Leaves c k a ->
                 {auto lower : LTE b c} ->
                 {auto upper : LTE c (2 * b)} ->
                 HNode 0 l b k a

         HInt  : Ord k => NodeLog e k a ->
                 Children c (pred d) l b k a ->
                 {auto pos   : LTE 1 b} ->
                 {auto lower : LTE b c} ->
                 {auto upper : LTE c (2 * b)} ->
                 {auto log   : LTE e l} ->
                 HNode d l b k a


data HTree : (l, b : Nat) -> (k, a : Type) -> Type where

     ||| Partial root node, acting like a leaf.
     Partial : Leaves c k a ->
               {auto lower : LTE 0 c} -> {auto upper : LTE c (2 * b)} ->
               HTree l b k a

     ||| Full root node, acting like an internal node.
     Full : NodeLog e k a -> Children c d l b k a ->
            -- {auto pos : LTE 1 2} ->
            {auto lower : LTE 2 c} ->
            {auto upper : LTE c (2 * b)} ->
            {auto log   : LTE e l} ->
            HTree l b k a


total
lookupOrdRange : Ord k => k -> Vect n (k, a) -> {auto pos : LTE 1 n} -> a
lookupOrdRange k0 ((_,a0) :: kas) = go a0 kas
  where
    go : a -> Vect m (k,a) -> a
    go a [] = a
    go a ((k, a') :: kas') =
        case compare k0 k of
             LT => a
             EQ => a'
             GT => go a' kas'


lookupLogs : Ord k => k -> HTree l b k a ->
             {auto two : LTE 2 b} ->
             Log k a
lookupLogs x ht =
    case ht of
         Partial lvs  => fromLeaves lvs
         Full lg chld => fromInt lg chld
  where
    fromNode : HNode d l b k a -> Log k a

    fromLeaves : Leaves c k a -> Log k a
    fromLeaves = fromMaybe [] . lookup x

    fromInt : NodeLog e k a ->
              Children c d l b k a ->
              {auto pos   : LTE 1 lb} ->
              {auto lower : LTE lb c} ->
              {auto upper : LTE c (2 * b)} ->
              {auto log   : LTE e l} ->
              Log k a
    fromInt lg chld {pos} {lower} =
        let (_ ** fromLg) = Vect.filter (\z => x == keyFor z) lg
            fromChld = fromNode (lookupOrdRange x chld {pos = lteTransitive pos lower}) in
            toList fromLg ++ fromChld

    fromNode (HLeaf lvs)    = fromLeaves lvs
    fromNode (HInt lg chld) = fromInt lg chld


empty : Ord k => {auto two : LTE 2 b} -> HTree l b k a
empty = Partial Nil


%access export

addLeaves : {res : Nat -> Nat -> Type -> Type -> Type} ->
            Ord k => (lb : Nat) -> (Leaves c' k a -> res l b k a) ->
            NodeLog e k a -> Leaves c k a ->
            {auto pos : LTE 1 b} ->
            {auto lower : LTE lb c} ->
            {auto upper : LTE lb b} ->
            Either (k, res l b k a) (Vect n (k, HNode 0 l b k a))


addInternal : {res : Nat -> Nat -> Type -> Type -> Type} ->
              Ord k => (lb : Nat) ->
              (NodeLog e' k a -> Children c' d l b k a -> res l b k a) ->
              NodeLog lc k a -> NodeLog e k a -> Children c d l b k a ->
              {auto p1 : 1 `LTE` lb} ->
              {auto p2 : lb `LTE` c} ->
              {auto p3 : c `LTE` 2 * b} ->
              {auto p4 : e `LTE` l} ->
              {auto p5 : lb `LTE` c'} ->
              {auto p6 : c' `LTE` 2 * b} ->
              {auto p7 : e' `LTE` l} ->
              Either (k, res l b k a) (Vect m (k, HNode (d + 1) l b k a))
-- addInternal lb mkRes lgAdd lg chld {e'} {l} {res} =
--     case isLTE (S l) e' of
--          Yes prf   => ?addInternal_rhs_rhs_1
--          No contra => let lg' = lgAdd ++ lg in Left (sameLevel lg' chld)
--   where
--     sameLevel : NodeLog e' k a -> Children c' d l b k a -> (k, res l b k a)


addLog : Ord k => NodeLog e k a -> HNode d l b k a ->
         {auto prf : LTE 1 b} ->
         (n ** Vect n (k, HNode d l b k a))
addLog lgAdd (HLeaf lvs)    = ?addLog_rhs_1
addLog lgAdd (HInt lg chld) = ?addLog_rhs_2


addStatements : Ord k => List (Statement k a) -> HTree l b k a ->
                {auto two : LTE 2 b} ->
                HTree l b k a
addStatements [] ht    = ht
addStatements stmts ht =
    let lgAdd = fromList stmts in
        case ht of
             Partial lvs  => ?addStatements_rhs_1
             Full lg chld => ?addStatements_rhs_2
  where
    handleOverflow : Vect n (k, HNode d l b k a) -> HTree l b k a
    checkOverflow : Either (k, HTree l b k a) (Vect n (k, HNode d l b k a)) -> HTree l b k a
    checkOverflow = either snd handleOverflow


fromList : Ord k => List (k,a) -> {auto two : LTE 2 b} -> HTree l b k a
fromList xs = addStatements (map (uncurry Assert) xs) empty


insert : Ord k => k -> a -> HTree l b k a ->
         {auto two : LTE 2 b} ->
         HTree l b k a
insert k a = addStatements [Assert k a]


delete : Ord k => k -> HTree l b k a -> {auto two : LTE 2 b} -> HTree l b k a
delete k = addStatements [Retract k]


addStatement : Ord k => Statement k a -> HTree l b k a ->
               {auto two : LTE 2 b} ->
               HTree l b k a
addStatement = addStatements . pure


lookup : Ord k => k -> HTree l b k a ->
         {auto two : LTE 2 b} ->
         Maybe a
lookup k ht = listToMaybe (lookupLogs k ht) >>= valueFor


adjustWithKey : Ord k => (k -> a -> a) -> k -> HTree l b k a ->
                {auto two : LTE 2 b} ->
                HTree l b k a
adjustWithKey f k ht = maybe ht (\v => insert k (f k v) ht) (lookup k ht)


adjust : Ord k => (a -> a) -> k -> HTree l b k a ->
         {auto two : LTE 2 b} ->
         HTree l b k a
adjust = adjustWithKey . const


updateWithKey : Ord k => (k -> a -> Maybe a) -> k -> HTree l b k a ->
                {auto two : LTE 2 b} ->
                HTree l b k a
updateWithKey f k ht =
    maybe ht (\v => addStatement (toStatement k (f k v)) ht) (lookup k ht)


update : Ord k => (a -> Maybe a) -> k -> HTree l b k a ->
         {auto two : LTE 2 b} ->
         HTree l b k a
update = updateWithKey . const


alter : Ord k => (Maybe a -> Maybe a) -> k -> HTree l b k a ->
        {auto two : LTE 2 b} ->
        HTree l b k a
alter f k ht = addStatement (toStatement k (f (lookup k ht))) ht


-- --------------------------------------------------------------------- [ EOF ]
