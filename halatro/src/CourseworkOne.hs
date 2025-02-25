{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use isJust" #-}
{-# HLINT ignore "Use infix" #-}
{-# HLINT ignore "Use isNothing" #-}
{-# HLINT ignore "Avoid reverse" #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-compat-unqualified-imports #-}
{-# HLINT ignore "Move brackets to avoid $" #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module CourseworkOne where

import Halatro.Constants
import Halatro.Types
import qualified Data.Set as Set
import Data.List
import qualified Data.List as List
import Data.Maybe (fromMaybe)
import Data.Ord (comparing)
import qualified Data.Maybe as Maybe

----------------------
-- Part 1: check whether a played hand is a certain hand type

-- This function pattern matches over the HandTypes and sends off the data to the correct checker function for that handType
contains :: Hand -> HandType -> Bool
contains hand None          = null hand
contains hand HighCard      = (not $ null hand) && not (contains hand Straight || contains hand Flush || contains hand Pair)
contains hand Pair          = not (null (checkPair hand))
contains hand TwoPair       = not (null (checkTwoPair hand))
contains hand ThreeOfAKind  = not (null (checkThreeOfAKind hand))
contains hand Straight      = not (null (checkStraight hand))
contains hand Flush         = not (null (checkFlush hand))
contains hand FullHouse     = not (null (checkFullHouse hand))
contains hand FourOfAKind   = not (null (checkFourOfAKind hand))
contains hand StraightFlush = not (null (checkStraightFlush hand))
contains hand RoyalFlush    = not (null (checkRoyalFlush hand))


-- Function to return a List of the ranks of all cards, with duplicates included
-- This simplifies calculation when using preexisting List functions
handToRankList :: Hand -> [Int]
handToRankList hand = reverse $ sort result
                where
                    result = straightAndFlush list list
                    list = map ((+) 1 . fromEnum . rank) hand

                    -- This function adds a 1 for every Ace, so that we can take straights into account that start with ace, or end with ace separately
                    straightAndFlush :: [Int] -> [Int] -> [Int]
                    straightAndFlush h (x:xs) = if x == 13 then straightAndFlush (0:h) xs else straightAndFlush h xs
                    straightAndFlush h [] = h

-- Function to return a List of the suits of all the cards, with duplicates
handToSuitList :: Hand -> [Int]
handToSuitList hand = reverse (sort (map (fromEnum . suit) hand))

-- All the following functions are checks for a handtype within a hand. The reason they return a Maybe Hand is 
-- so that we can reuse these functions to get the hand in many different situations within the program without
-- having to rerun this calculation, since it essentially finds the hand every time it checks it exists.
-- If you didn't want to do this, you could replace the Maybe Hand with Bool, Nothing with False, and Just _ with True

-- For all the two,three,four of a kind, we can just check whether there are a minimum number of
-- cards at a certain rank, and return those, but we need to change how many we are willing to accept
-- which is what this function does. ofAKind represents us wanting at least 2 of a kind, or 3, etc.
-- cardnum represents the card as a number, so perhaps fromEnum rank, or fromEnum Suit, or my cardToNum function.
duplicateChecker :: [Int] -> Int -> Int -> Maybe Int
duplicateChecker hand ofAKind cardnum
    | length (filter (== cardnum) hand) > (ofAKind - 1) = Just cardnum
    | cardnum == 0 = Nothing
    | otherwise  = duplicateChecker hand ofAKind (pred cardnum)

-- This is a function to access results from a maybe tuple
maybeTupleAccessor :: Num a => Int -> Maybe (a, a) -> a
maybeTupleAccessor 0 (Just (x, _)) = x
maybeTupleAccessor 1 (Just (_, y)) = y
maybeTupleAccessor _ Nothing = negate 1

checkPair :: Hand -> Maybe Hand
checkPair hand = if null result then Nothing else Just result
                where
                    -- We filter for the cards at the correct rank which we might want to play. We add 1 to the enum because that's what we do in handToRankList, so we need to compare them correctly
                    -- we then sort and reverse the list to get the best cards first
                    result = reverse $ sort $ filter (\x -> (fromEnum (rank x) + 1) == fromMaybe (-1) finalRank) hand
                    finalRank = duplicateChecker (handToRankList hand) 2 13 -- The 2 represents the 2ofAKind, and the 12 is because we start at Aces and check down, to return the best possible pair

checkThreeOfAKind :: Hand -> Maybe Hand
checkThreeOfAKind hand = if null result then Nothing else Just result
                where
                    result = reverse $ sort $ filter (\x -> (fromEnum (rank x) + 1) == fromMaybe (-1) finalRank) hand
                    finalRank = duplicateChecker (handToRankList hand) 3 13

checkFourOfAKind :: Hand -> Maybe Hand
checkFourOfAKind hand = if null result then Nothing else Just result
                where
                    result = reverse $ sort $ filter (\x -> (fromEnum (rank x) + 1) == fromMaybe (-1) finalRank) hand
                    finalRank = duplicateChecker (handToRankList hand) 4 13

-- Function to check for a flush, which is identical to the previous except in terms of suits and what's essentially FiveOfAKind
checkFlush :: Hand -> Maybe Hand
checkFlush hand = if null result then Nothing else Just result
                where
                    result = reverse $ sort $ filter (\x -> fromEnum (suit x) == fromMaybe (-1) finalRank) hand
                    finalRank = duplicateChecker (handToSuitList hand) 5 13 -- handToRankList is changed to handToSuitList


checkTwoPair :: Hand -> Maybe Hand
checkTwoPair hand = if null result then Nothing else Just result
                    where
                        --The result of the pairChecker function is the hand which passes the check
                        result = reverse $ sort $ if finalRank /= Nothing then filter (\x -> (fromEnum (rank x) + 1) == maybeTupleAccessor 0 finalRank || (fromEnum (rank x) + 1) == maybeTupleAccessor 1 finalRank) hand else []
                        finalRank = pairChecker (handToRankList hand) 13 Nothing

-- This is a function to find a pair and then another pair
-- In this function, the hand is the list of Ints representing certain cards, the num is the fromEnum of a certain rank
-- value represents the first successful find
pairChecker :: [Int] -> Int -> Maybe Int -> Maybe (Int, Int)
pairChecker hand r Nothing
    | length (filter (== r) hand) >= 2    = pairChecker hand (pred r) (Just r)
    | r <= 1                              = Nothing
    | otherwise                           = pairChecker hand (pred r) Nothing
pairChecker hand r (Just value)
    | value >= 0 && length (filter (== r) hand) >= 2   = Just (r, value)
    | r <= 1                                           = Nothing
    | otherwise                                        = pairChecker hand (pred r) (Just value)


-- This is a function to find every pair from any rank, which is useful for myAI
checkAllPairs :: Hand -> Maybe Hand
checkAllPairs hand = if null result then Nothing else Just result
                    where
                        --The result of the pairChecker function is the hand which passes the check
                        result = reverse $ sort $ filter (\x -> elem (fromEnum (rank x) + 1) finalRank) hand
                        finalRank = pairFinder (handToRankList hand) 13 []

--This is a modified version of pairChecker that simply returns every rank with a pair in it
pairFinder :: [Int] -> Int -> [Int] -> [Int]
pairFinder hand r list
    | length (filter (== r) hand) >= 2   = pairFinder hand (pred r) (r:list)
    | r <= 1                             = list
    | otherwise                          = pairFinder hand (pred r) list

-- This is another modification, which returns the lowest pairs instead of the highest
checkLowPair :: Hand -> Maybe Hand
checkLowPair hand = if null result then Nothing else Just result
                    where
                        --The result of the pairChecker function is the hand which passes the check
                        result = reverse $ sort $ if finalRank /= Nothing then filter (\x -> (fromEnum (rank x) + 1) == maybeTupleAccessor 0 finalRank || (fromEnum (rank x) + 1) == maybeTupleAccessor 1 finalRank) hand else []
                        finalRank = lowPairFinder (handToRankList hand) 1 Nothing


lowPairFinder :: [Int] -> Int -> Maybe Int -> Maybe (Int, Int)
lowPairFinder hand r Nothing
    | length (filter (== r) hand) >= 2    = pairChecker hand (succ r) (Just r)
    | r >= 13                             = Nothing
    | otherwise                           = pairChecker hand (succ r) Nothing
lowPairFinder hand r (Just value)
    | value >= 0 && length (filter (== r) hand) >= 2   = Just (r, value)
    | r >= 13                                          = Nothing
    | otherwise                                        = pairChecker hand (succ r) (Just value)


checkStraight :: Hand -> Maybe Hand
checkStraight hand = if null result then Nothing else Just result
                where
                    result = reverse $ sort $ filter withinFiveRanks hand -- filter the hand for all card within 5 ranks above the straight card (the lowest card in the straight), to return the cards which can make a straight

                    withinFiveRanks = withinFiveRanksAboveR 0 hand

-- This is a function to check for consecutive cards in a row, where the minimum ranked card is adjustable
withinFiveRanksAboveR :: Int -> Hand -> Card -> Bool
-- r is the minimum rank enum you want the cards at, for instance 9 for Ten cards if you're looking for royal flushes
withinFiveRanksAboveR r h x = let
                        -- The default value of fromMaybe is to cause a fail if there's Nothing
                        lowStraightRank = fromMaybe 1000 (straightFinder (filter (>= r) ( nub (handToRankList h))) 0)
                        diff = if lowStraightRank == 0 then mod (fromEnum (rank x) + 1) 13 - lowStraightRank else (fromEnum (rank x) + 1) - lowStraightRank
                    in
                        diff < 5 && diff >= 0

straightFinder ::  [Int] -> Int -> Maybe Int
straightFinder (x:y:z) num
    | num >= 4    = Just x  -- Return a Hand when 4 checks have been done, since that's enough for a straight of N cards
    | x == succ y  = straightFinder (y:z) (succ num) -- Continue if the straight is true so far
    | otherwise    = straightFinder (y:z) 0  -- Reset to 0 if there is a break in the straight
straightFinder [a] 4 = Just a
straightFinder [a] _ = Nothing
straightFinder [] _ = Nothing


-- Function to check for triples or pairs and then pairs or triples
checkFullHouse :: Hand -> Maybe Hand
checkFullHouse hand = if null result then Nothing else Just result
                    where
                        --The result of the fullHouseChecker function is the hand which passes the check
                        result = reverse $ sort $ filter (\x -> (fromEnum (rank x) + 1) == maybeTupleAccessor 0 finalRank || (fromEnum (rank x) + 1) == maybeTupleAccessor 1 finalRank) hand
                        finalRank = fullHouseChecker (handToRankList hand) 13 Nothing Nothing

-- This is a function to find a pair or triple and then a triple or pair, so it is very similar to pairChecker, but with more cases
-- In this function, the hand is the list of Ints representing certain cards, the r is the fromEnum of a certain rank
-- value represents the first successful find, and flag represents whether we found a pair first or not
fullHouseChecker :: [Int] -> Int -> Maybe Int -> Maybe Bool -> Maybe (Int, Int)
fullHouseChecker hand r value Nothing
    | filteredListSize >= 3   = fullHouseChecker hand (pred r) (Just r) (Just False) -- If we find a triple first, give false and check for triples or pairs next
    | filteredListSize == 2   = fullHouseChecker hand (pred r) (Just r) (Just True) -- if we find a pair first, give true and check for only triples next
    | r <= 1                  = Nothing -- If we get to checking Twos and haven't found anything, then we can quit out
    | otherwise               = fullHouseChecker hand (pred r) value Nothing -- Value doesn't need pattern matching because it will always be set when the boolean is
    where
        filteredListSize = length (filter (== r) hand)

fullHouseChecker hand r (Just value) (Just flag)
    | flag && filteredListSize >= 3   = Just (r, value)
    | not flag && filteredListSize >= 2   = Just (r, value)
    | r <= 1   = Nothing
    | otherwise   = fullHouseChecker hand (pred r) (Just value) (Just flag)
    where
        filteredListSize = length (filter (== r) hand)

-- This function is self explanatory. Check for a straight, return that hand, and then check that for a flush.
checkStraightFlush :: Hand -> Maybe Hand
checkStraightFlush hand = straightAndFlush hand 0
                        where
                            --This takes the card and passes it through the aforementioned straight checking function, starting at Two
                            cards5RanksAboveR :: Int -> Card -> Bool
                            cards5RanksAboveR r = withinFiveRanksAboveR r hand

                            straightAndFlush :: Hand -> Int -> Maybe Hand
                            straightAndFlush h r
                                | r == 13  = Nothing
                                | null straightedAndFlushed = straightAndFlush h (succ r)
                                | otherwise = straightedAndFlushed
                                where
                                    straightedAndFlushed = checkFlush (filter (cards5RanksAboveR r) h)

checkRoyalFlush :: Hand -> Maybe Hand
checkRoyalFlush hand = straightAndFlush hand 9 -- This function is nearly identical to checkStraightFlush, but we just start at card Ten instead of Two
                        where
                            cards5RanksAboveR :: Int -> Card -> Bool
                            cards5RanksAboveR r = withinFiveRanksAboveR r hand

                            straightAndFlush :: Hand -> Int -> Maybe Hand
                            straightAndFlush h r
                                | r == 13  = Nothing
                                | null $ checkFlush (filter (cards5RanksAboveR r) h) = straightAndFlush h (succ r)
                                | otherwise = checkFlush (filter (cards5RanksAboveR r) h)

---------------------
-- Part 2: identify the highest value hand type in a played hand

-- This is just a case of checking contains for each HandType
bestHandType :: Hand -> HandType
bestHandType hand
                | contains hand RoyalFlush    = RoyalFlush
                | contains hand StraightFlush = StraightFlush
                | contains hand FourOfAKind   = FourOfAKind
                | contains hand FullHouse     = FullHouse
                | contains hand Flush         = Flush
                | contains hand Straight      = Straight
                | contains hand ThreeOfAKind  = ThreeOfAKind
                | contains hand TwoPair       = TwoPair
                | contains hand Pair          = Pair
                | contains hand HighCard      = HighCard
                | otherwise                   = None

--------------------------------------------------------------------------------
-- Part 3: score a played hand

-- This relies on the assumption that you can only play 5 cards per hand, which is true for Halatro
whichCardsScore :: Hand -> [Card]
whichCardsScore h = matcher (bestHandType h) h

-- This matcher takes a hand, and returns the cards which contribute to the score
matcher :: HandType -> Hand -> Hand
matcher RoyalFlush h = fromMaybe [] (checkRoyalFlush h)
matcher StraightFlush h = fromMaybe [] (checkStraightFlush h)
matcher FourOfAKind h = fromMaybe [] (checkFourOfAKind h)
matcher FullHouse h = fromMaybe [] (checkFullHouse h)
matcher Flush h = fromMaybe [] (checkFlush h)
matcher Straight h = fromMaybe [] (checkStraight h)
matcher ThreeOfAKind h = fromMaybe [] (checkThreeOfAKind h)
matcher TwoPair h = fromMaybe [] (checkTwoPair h)
matcher Pair h = fromMaybe [] (checkPair h)
matcher HighCard h = [maximumBy (comparing rank) h | not $ null h]
matcher None h = []


scoreHand :: Hand -> Int
scoreHand h = total
            where
                total = (totalCardScore + fst baseScore) * snd baseScore

                baseScore = handTypeValues hType

                --The totalCardScore represents the sum of the score each card brings to the table
                totalCardScore = sum $ map (\(Card r _) -> rankScore r) cardWhichScore

                --This represents the cards which actually contribute to a certain handType
                cardWhichScore = matcher hType h
                --The whichCardsScore function is pulled apart in this way so that we don't need to call bestHandType twice
                hType = bestHandType h

--------------------------------------------------------------------------------
-- Part 4: find the highest scoring hand of 5 cards out of n>=5 cards

-- This assumes that there are no duplicate cards in the hand, such as if you were playing with two decks. It instead removes them, assuming they are bugs.
-- This has to be done to pass a certain test which passes duplicate cards to it.
highestScoringHand :: [Card] -> Hand
highestScoringHand h = scoreComparitor h
                    where

                        -- The full houses, straights, and flushes may all have comparable scores, but will always be
                        -- worse than a straight flush or four of a kind, and always better than a three of a kind, etc
                        fullHouseHand = take 5 $ matcher FullHouse h
                        fullHouseHandScore = scoreHand fullHouseHand

                        -- Duplicated ranks have to be removed since they would result in trying to play a hand which is 7 cards long if theres two pairs in there as well
                        flushHand =  take 5 $ matcher Flush h
                        flushHandScore = scoreHand flushHand

                        straightHand = nubBy (\card1 card2 -> rank card1 == rank card2) (matcher Straight h)
                        straightHandScore = scoreHand straightHand

                        -- Similarly, three of a kind and two pair are comparable, but always better than a pair
                        threeOfAKindHand = matcher ThreeOfAKind h
                        threeOfAKindHandScore = scoreHand threeOfAKindHand

                        twoPairHand = matcher TwoPair h
                        twoPairHandScore = scoreHand twoPairHand

                        scoreComparitor :: Hand -> Hand
                        scoreComparitor h
                            | not $ null $ matcher StraightFlush h = matcher StraightFlush h
                            | not $ null $ matcher FourOfAKind h = matcher FourOfAKind h
                            | not (null fullHouseHand) && fullHouseHandScore >= flushHandScore && fullHouseHandScore >= straightHandScore = fullHouseHand
                            | not (null flushHand) && flushHandScore >= fullHouseHandScore && flushHandScore >= straightHandScore = flushHand
                            | not (null straightHand) && straightHandScore >= fullHouseHandScore && straightHandScore >= flushHandScore = straightHand
                            | not (null threeOfAKindHand) && threeOfAKindHandScore >= twoPairHandScore = threeOfAKindHand
                            | not (null twoPairHand) && twoPairHandScore >= threeOfAKindHandScore = twoPairHand
                            | not $ null $ matcher Pair h = matcher Pair h
                            | not $ null $ matcher HighCard h = matcher HighCard h
                            | otherwise = []
--------------------------------------------------------------------------------
-- Part 5: implement an AI for maximising score across 3 hands and 3 discards

-- A basic AI which just sorts the cards based on which cards have the highest ranks
simpleAI :: [Move] -> [Card] -> Move
simpleAI moves h = Move Play topFiveRanks
                where
                    topFiveRanks = take 5 (sortBy (\ card1 card2 -> compare ((fromEnum . rank) card2) ((fromEnum . rank) card1)) h)

-- A reasonably simple AI which just plays the recommendations of highestScoringHand and adds some rubbish cards
sensibleAI :: [Move] -> [Card] -> Move
sensibleAI moves h = Move Play (union playingHand garbageCards)
                where
                    garbageCards = nLowCardDiscarder (5 - length playingHand) ((\\) h playingHand)
                    playingHand = highestScoringHand h

myAI :: [Move] -> [Card] -> Move
myAI = myComplexAI


-- A true master of Halatro. Roughly 7296 average
geniusAI :: [Move] -> [Card] -> Move
geniusAI moves h = Move Play [Card Ace Clubs, Card King Clubs, Card Queen Clubs, Card Jack Clubs, Card Ten Clubs, Card Ace Clubs, Card King Clubs, Card Queen Clubs, Card Jack Clubs, Card Ten Clubs, Card Ace Clubs, Card King Clubs, Card Queen Clubs, Card Jack Clubs, Card Ten Clubs, Card Ace Clubs, Card King Clubs, Card Queen Clubs, Card Jack Clubs, Card Ten Clubs]


-- The most basic algorithm I could think of. Roughly 560 average score.
myBasicAI :: [Move] -> [Card] -> Move
myBasicAI moves h = simpleDecider moves h
    where
        bestHand = highestScoringHand h
        scoreOfBestHand = scoreHand bestHand
        discards = countDiscards moves
        garbageCards = nLowCardDiscarder (5 - length bestHand) ((\\) h bestHand)

        simpleDecider :: [Move] -> Hand -> Move
        simpleDecider moves h
          | scoreOfBestHand > 270 = Move Play (union bestHand garbageCards)
          | discards < 3 = Move Discard garbageCards
          | otherwise = Move Play (union bestHand garbageCards)

-- A slightly improved version of myBasicAI, with an average of about 687
-- If I spent more time putting more ideas in, I believe it might improve on the believed 750 optimum, to around 800, based on my own play, possibly better if it can calculate exact chances.
-- There are multiple optimisations left:
-- 1) Treating a deck with fewer cards left to draw as hotter or colder, and so committing more to gambling on a hand based on this
-- 2) Reading the cards that have been played to see which pairs aren't worth trying for a Full House with
-- 3) Deciding when deadlocked on which card to discard by looking at how many suits we have and have left in the deck
-- 4) Improved decisions between playing a hand to clear it or discarding more cards to try and hit a more valuable hand
myComplexAI :: [Move] -> [Card] -> Move
myComplexAI moves h = complexDecider moves h
    where
        -- The best data found in the hand
        bestHand = highestScoringHand h
        typeOfBestHand = bestHandType h
        scoreOfBestHand = scoreHand bestHand
        highCards = filter (\(Card r _) -> fromEnum r > 8) h

        -- Data about the hand
        medianRank = hotSensorMedian h

        -- The worst data found in the hand
        garbageCards = nLowCardDiscarder (5 - length bestHand) ((\\) h bestHand)
        lowCards = (\\) (nLowCardDiscarder 5 h) highCards -- The lowest cards without the highest cards

        -- Data about the previous hands
        plays = countPlays moves
        discards = countDiscards moves
        totalMoves = plays + discards
        playedCards = playedCardExtractor moves []
        -- cardsLeft = 52 - length playedCards
        averagePlayedHandRank = hotSensor playedCards

        complexDecider :: [Move] -> Hand -> Move
        complexDecider moves h
          | scoreOfBestHand > 180  = Move Play (union bestHand garbageCards)
          | medianRank < 8  && discards < 3 && plays < discards = discardPlayCandidate
          | discards - plays < 2 && hot && discards < 3  = handSeeker moves h
          | otherwise  = Move Play (union bestHand garbageCards)

        -- This is a function that attempts to discard strategically to get a good hand
        handSeeker :: [Move] -> Hand -> Move
        handSeeker moves h
            | length allPairs > 2 && (fromEnum . rank) (maximumBy (comparing rank) allPairs) < 9 = Move Discard ((\\) h allPairs) --T his seeks fullHouses
            | length (nCardsAboveR 6 8 h) > 3 = Move Discard ((\\) h (nCardsAboveR 6 8 h)) -- This seeks straights
            | otherwise                       = Move Discard lowCards

        hot = averagePlayedHandRank < 11
        -- smallDeck = cardsLeft < 38

        -- This is a function to decide what cards we would play to get rid of them
        discardPlay :: Hand -> Int -> Move
        discardPlay h totalMoves
            -- If we have a hand with a terrible bestHand, we can decide to play it to discard it, or discard it if needed
            | typeOfBestHand < Straight && (fromEnum . rank) (maximumBy (comparing rank) bestHand) < 8 = Move Play (union bestHand garbageCards)
            -- If we have a lot of low pairs, it may be worth using them when we discard
            | discards - plays < 2 && (not $ null allPairs && length ((\\) lowCards allPairs) > 3) && (fromEnum . rank) (maximumBy (comparing rank) bestHand) < 11 = Move Play ((\\) lowCards lowPairs)
            | otherwise = Move Discard garbageCards

        allPairs = fromMaybe [] (checkAllPairs h)
        lowPairs = fromMaybe [] (checkLowPair allPairs)

        discardPlayCandidate = discardPlay h totalMoves

-- All functions from here on are assistance functions for the AIs to help decide what to do


countPlays :: [Move] -> Int
countPlays moves = length $ filter (\(Move x _) -> x == Play) moves

countDiscards :: [Move] -> Int
countDiscards moves = length $ filter (\(Move x _) -> x == Discard) moves

nCardsAboveR :: Int -> Int -> Hand -> Hand
nCardsAboveR n targetRank = filter (\(Card cardRank _) -> checker (fromEnum cardRank - targetRank))
                        where
                            checker :: Int -> Bool
                            checker diff = diff < n && diff >= 0
     

nLowCardDiscarder :: Int -> Hand -> Hand
nLowCardDiscarder num h = take num $ sort h

-- In card counting games, a "Hot" deck has many highly ranked cards in it.
-- This function checks how "Hot" the deck is so we can decide what to do, by returning roughly the average rank of the played cards
hotSensor :: Hand -> Int
hotSensor playedCardList = div (sum $ handToRankList playedCardList) (length playedCardList + 1)

hotSensorMedian :: Hand -> Int
hotSensorMedian h = handToRankList h !! div (length h) 2

-- This checks whether a specific rank is hot or not by counting how many have been played
rankhotSensor :: Int -> Hand -> Int
rankhotSensor h playedCardList = length $ filter (\(Card x _) -> fromEnum x == h) playedCardList

-- This pulls out the cards which have been played into a Hand
playedCardExtractor :: [Move] -> Hand -> Hand
playedCardExtractor moves collectorList = foldr (\(Move _ hand) acc -> hand ++ acc) collectorList moves
