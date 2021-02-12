module Dist where

import Data.List( insert, sort, sortBy )
import Data.Ord( comparing )

data Dist
  = Dist
  { val  :: Double
  , dist :: [Piece] -- strictly ordered
  }
 deriving ( Eq, Ord, Show )

data Piece
  = Line{ start :: (Double,Double), end_ :: (Double,Double) } -- open, >0
  | Point{ start :: (Double,Double) }
 deriving ( Eq, Show )

end :: Piece -> (Double, Double)
end (Line _ p) = p
end (Point p) = p

value, distance :: (Double, Double) -> Double
value = fst
distance = snd

segment :: (Double, Double) -> (Double, Double) -> [Piece]
segment p q = segments (sortBy (comparing value) [p, q])

segments :: [(Double, Double)] -> [Piece]
segments [p] = [Point p]
segments (p:q:ps) | value p == value q =
  segments $ (if distance p < distance q then p else q):ps
segments (p:q:ps) = Point p:Line p q:segments (q:ps)

squareRootPieces :: Double -> Double -> [Piece]
squareRootPieces a c =
  segments [(a, sqrt a), (b, sqrt b), (c, sqrt c)]
  where
    b = sqrt(a*c)/2 + (a+c)/4 -- minimises absolute error

holding :: ((Double, Double) -> (Double, Double) -> (Double, Double)) -> Piece -> Piece -> [Piece]
holding f (Point p) (Point q) =
  [Point (f p q)]
holding f (Point p) (Line q1 q2) =
  segment (f p q1) (f p q2)
holding f (Line p1 p2) (Point q) =
  segment (f p1 q) (f p2 q)
holding f (Line p1 p2) (Line q1 q2) =
  segment (f p1 q1) (f p1 q2) ++
  segment (f p2 q1) (f p2 q2) ++
  segment (f p1 q1) (f p2 q1) ++
  segment (f p1 q2) (f p2 q2)

distAdd :: Dist -> Dist -> Dist
distAdd = lift2 (holding (\(x1, d1) (x2, d2) -> (x1+x2, d1+d2)))

distMul :: Dist -> Dist -> Dist
distMul = lift2 pieceMul
  where
    pieceMul p q =
      squareRootPiece p q ++
      holding (\(x1, d1) (x2, d2) -> (x1 * x2, d1 + d2)) p q

    squareRootPiece l1@(Line (x1, d1) (x2, d2)) l2@(Line (y1, e1) (y2, e2))
      | x1 == x2 || y1 == y2 || d1 == d2 || e1 == e2 = []
      | otherwise =
        map (scale (a*b)) (squareRootPiece' (scale (1/a) l1) (scale (1/b) l2))
      where
        a = (d2-d1)/(x2-x1)
        b = (e2-e1)/(y2-y1)
    squareRootPiece _ _ = []

    squareRootPiece' (Line (x1, d1) (x2, d2)) (Line (y1, e1) (y2, e2))
      | z1 < z2 = map (addDistance (d + e)) (squareRootPieces z1 z2)
      | otherwise = []
      where
        z1 = x1 `max` y1
        z2 = x2 `min` y2
        d = d1 + (z1 - x1) * (d2 - d1) / (x2 - x1)
        e = e1 + (x2 - y1) * (e2 - e1) / (y2 - y1)

scale :: Double -> Piece -> Piece
scale a (Point (x, d)) = Point (a*x, d)
scale a (Line (x1, d1) (x2, d2))
  | a == 0    = Point (0, d1 `min` d2)
  | a < 0     = Line (x2*a, d2) (x1*a, d1)
  | otherwise = Line (x1*a, d1) (x2*a, d2)

addDistance :: Double -> Piece -> Piece
addDistance a (Point (x, d)) = Point (x, a+d)
addDistance a (Line (x1, d1) (x2, d2)) = Line (x1, d1+a) (x2, d2+a)

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

