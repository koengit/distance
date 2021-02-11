module Dist where

import Data.List( insert, sort )

data Dist
  = Dist
  { val  :: Double
  , dist :: [Piece] -- strictly ordered
  }
 deriving ( Eq, Ord, Show )

data Piece
  = Line{ start :: (Double,Double), end :: (Double,Double) } -- open, >0
  | Point{ start :: (Double,Double) }
 deriving ( Eq, Show )

instance Ord Piece where
  p `compare` q = (start p, mslope p) `compare` (start q, mslope q)
   where
    mslope (Line (x,a) (y,b)) = Just ((b-a) / (y-x))
    mslope _                  = Nothing

constant :: Double -> Dist
constant x = Dist x [Point (x,0)]

input :: (Double,Double) -> Double -> Dist
input (a,b) x
 | a == x         = Dist x [Point (x,0),Line (a,0) (b,b-a),Point (b,b-a)]
 | b == x         = Dist x [Point (a,b-a),Line (a,b-a) (b,0),Point (x,0)]
 | a < x && x < b = Dist x [Point (a,x-a),Line (a,x-a) (x,0),Point (x,0),Line (x,0) (b,b-x)]
 | otherwise      = error "input out of bounds"

lift2 :: (Piece -> Piece -> [Piece]) -> Dist -> Dist -> Dist
lift2 f a b =
  Dist
  { val  = f0 (val a) (val b)
  , dist = norm [ r | p <- dist a, q <- dist b, r <- f p q ]
  }
 where
  f0 x y = let [Point (z,_)] = f (Point (x,0)) (Point (y,0)) in z

norm :: [Piece] -> [Piece]
norm ps = linesAndPoints (twoPoints (sort ps))
 where
  -- remove Points that are on the same x
  twoPoints (p@(Point (x1,_)) : Point (x2,_) : ps)
    | x1 == x2       = twoPoints (p : ps)
  twoPoints (p : ps) = p : twoPoints ps
  twoPoints []       = []
  
  -- a single Point at the beginning does not interfere with anything
  linesAndPoints (p@(Point _) : ps) =
    p : linesAndPoints ps
  
  -- a Line and something that lies beyond the Line: commit to the Line
  linesAndPoints (l@(Line _ (x2,_)) : p : ps)
    | fst (start p) >= x2 =
      l : linesAndPoints (p : ps)
  
  -- a Line and a Point: break the line if necessary
  linesAndPoints (l@(Line (x1,a1) (x2,a2)) : p@(Point (x,a)) : ps)
    | a' <= a =
      linesAndPoints (l : ps)

    | otherwise =
      Line (x1,a1) (x,a') : p : linesAndPoints (insert (Line (x,a') (x2,a2)) ps)
   where
    a' = l `at` x
  
  -- two Lines with the second Line starting somewhere below/on(-downwards) the first
  linesAndPoints (l@(Line (x1,a1) (x2,a2)) : m@(Line (y1,b1) (y2,b2)) : ps)
    | b1 < a' || (b1 == a' && (m `at` x2) <= a2) =
      Line (x1,a1) (y1,a') : Point (y1,a') :
        linesAndPoints (m : insert (Line (y1,a') (x2,a2)) ps)
   where
    a' = l `at` y1
  
  -- two Lines with the second Line starting somewhere above/on(-upwards) the first
  linesAndPoints (l@(Line (x1,a1) (x2,a2)) : m@(Line (y1,b1) (y2,b2)) : ps) =
    case l `cross` m of
      -- if they cross, cut off the bit above the first Line from the second
      Just x ->
        linesAndPoints (l : insert (Line (x,a) (y2,b2)) ps) 
       where
        a = l `at` x  
  
      -- if they don't cross, maybe keep the bit of the second Line that is longer than the first
      Nothing
        | y2 <= x2  -> linesAndPoints (l : ps) 
        | otherwise -> linesAndPoints (l : insert (Point (x2,a)) (insert (Line (x2,a) (y2,b2)) ps))
       where
        a = m `at` x2
      
  Line (x1,a1) (x2,a2) `at` x =
    a1 + (x - x1) * (a2 - a1) / (x2 - x1)
  
  Line (x1,a1) (x2,a2) `cross` Line (y1,b1) (y2,b2)
    | s1 == s2                             = Nothing
    | x1 < x && x < x2 && y1 < x && x < y2 = Just x
    | otherwise                            = Nothing
   where
    s1 = (a2-a1) / (x2-x1)
    s2 = (b2-b1) / (y2-y1)
    x  = (s2*y1 - s1*x1 + a1 - b1) / (s2-s1)  

