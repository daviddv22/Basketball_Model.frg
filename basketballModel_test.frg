
#lang forge/bsl

open "basketballModel.frg"

//wellFormedGame
assert all g: Game | nonnegstatg[g] is necessary for wellFormedGame[g]
assert all g: Game | wellFormedGame[g] is sufficient for nonnegstatg[g]

assert all g: Game | wellFormedPlayers[g] is necessary for wellFormedGame[g]
assert all g: Game | wellFormedGame[g] is sufficient for wellFormedPlayers[g]

assert all g: Game | wellFormedPossession[g] is necessary for wellFormedGame[g]
assert all g: Game | wellFormedGame[g] is sufficient for wellFormedPossession[g]

assert all g: Game | wellFormedScoreAndTime[g] is necessary for wellFormedGame[g]
assert all g: Game | wellFormedGame[g] is sufficient for wellFormedScoreAndTime[g]

//init
assert all g: Game | wellFormedGame[g] is necessary for init[g]
assert all g: Game | wellFormedPlayers[g] is necessary for init[g]
assert all g: Game | wellFormedPossession[g] is necessary for init[g]
assert all g: Game | wellFormedScoreAndTime[g] is necessary for init[g]

assert all g: Game | nonnegstatg[g] is necessary for init[g]
assert all g: Game | init[g] is sufficient for nonnegstatg[g]

//winner

assert all g: Game | notie[g] is necessary for winner[g]
assert all g: Game | notie[g] is sufficient for winner[g]

//tie 

assert all g: Game | nowinner[g] is necessary for tie[g]
assert all g: Game | nowinner[g] is sufficient for tie[g]

//valid score 

assert all g, g2: Game | nextPossession[g,g2] is sufficient for validScore[g] 
assert all g, g2: Game | nextPossession[g,g2] is sufficient for validScore[g2] 

assert all g, g2: Game | validScore[g] is necessary for nextPossession[g,g2]
assert all g, g2: Game | validScore[g2] is necessary for nextPossession[g,g2] 
//next possession

assert all g, g2: Game | wellFormedGame[g] is necessary for nextPossession[g,g2]
assert all g, g2: Game | wellFormedPlayers[g] is necessary for nextPossession[g,g2]
assert all g, g2: Game | wellFormedPossession[g] is necessary for nextPossession[g,g2]
assert all g, g2: Game | wellFormedScoreAndTime[g] is necessary for nextPossession[g,g2]

assert all g, g2: Game | wellFormedGame[g2] is necessary for nextPossession[g,g2]
assert all g, g2: Game | wellFormedPlayers[g2] is necessary for nextPossession[g,g2]
assert all g, g2: Game | wellFormedPossession[g2] is necessary for nextPossession[g,g2]
assert all g, g2: Game | wellFormedScoreAndTime[g2] is necessary for nextPossession[g,g2]

assert all g, g2: Game | nextPossession[g,g2] is sufficient for wellFormedGame[g]
assert all g, g2: Game | nextPossession[g,g2] is sufficient for wellFormedGame[g2]
assert all g, g2: Game | notOddScore[g,g2] is necessary for nextPossession[g,g2]
assert all g, g2: Game | nextPossession[g,g2] is sufficient for notOddScore[g,g2] 

assert all g, g2: Game | nextValidTimeAndScore[g,g2] is necessary for nextPossession[g,g2]
assert all g, g2: Game | nextValidScoring[g,g2] is necessary for nextPossession[g,g2]

test expect {
    wellFormedGame_sat: {
        all g: Game | {
            wellFormedGame[g]
        }
    } is sat

    wellFormedGame_sat_no_win: {
        all g: Game | {
            wellFormedGame[g]
            nowinner[g]
        }
    } is sat

    wellFormedPlayers_sat: {
        all g: Game | {
            wellFormedPlayers[g]
        }
    } is sat

    wellFormedPossession_sat: {
        all g: Game | {
            wellFormedPossession[g]
        }
    } is sat

    wellFormedScoreAndTime_sat: {
        all g: Game | {
            wellFormedScoreAndTime[g]
        }
    } is sat

    subPredWithWellFormedGame_sat: {
        all g: Game | {
            wellFormedGame[g]
            wellFormedPlayers[g]
            wellFormedPossession[g]
            wellFormedScoreAndTime[g]
        }
    } is sat

    winnerparadox: {
        some g: Game | {
            nowinner[g]
            notie[g]
        }
    } is unsat

    initnotwellformed: {
        some g: Game | {
            notWellFormed[g]
            init[g]
        }
    } is unsat

    goodpossession: {
        all g, g2: Game | {
            nextPossession[g, g2] => (validScore[g] and validScore[g2])
        }
    } is sat

    badpossession: {
        all g, g2: Game | {
            not nextPossession[g, g2] => oddScore[g, g2]
        }
    } is sat

    noBadScores: {
        some g, g2: Game | {
            nextPossession[g, g2]
            oddScore[g, g2]
        }
    } is unsat

    nextValidTimeAndScore_sat: {
        all g, g2: Game | {
            nextPossession[g, g2] => nextValidTimeAndScore[g, g2]
        }
    } is sat

    nextValidScoring_sat: {
        all g, g2: Game | {
            nextPossession[g, g2] => nextValidScoring[g, g2]
        }
    } is sat

    specificTestNextPossession: {
        all g, g2: Game | all disj t1, t2: Team | {
            nextPossession[g, g2]
            g.homeScore = 0
            g.awayScore = 0
            g.possession = t1
            g.playerWithBall = t1.pg
            g.time = 7
            g2.homeScore = 0
            g2.awayScore = 0
            g2.possession = t2
            g2.playerWithBall = t2.pg
            g2.time = 6
        }
    } is sat

    specificTestNextPossession_unsat: {
        some g, g2: Game | some t1, t2: Team | {
            nextPossession[g, g2]
            g.homeScore = 0
            g.awayScore = 0
            g.possession = t1
            g.playerWithBall = t1.pg
            g.time = 7
            g2.homeScore = 0
            g2.awayScore = 0
            g2.possession = t2
            g2.playerWithBall = t2.pg
            g2.time = 7
        }
    } is unsat
    
    specificInitTest: {
        all g: Game | all t1: Team | {
            init[g]
            g.homeScore = 0
            g.awayScore = 0
            g.possession = t1
            g.playerWithBall = t1.pg
            g.time = 7
        }
    } is sat

    specificInitTest_unsat: {
        some g: Game | some t1: Team | {
            init[g]
            g.homeScore = 1
            g.awayScore = 0
            g.possession = t1
            g.playerWithBall = t1.pg
            g.time = 7
        }
    } is unsat

    specificWinnerTest: {
        all g: Game | all t1: Team | {
            winner[g]
            g.homeScore = 0
            g.awayScore = 2
            g.possession = t1
            g.playerWithBall = t1.pg
            g.time = 0
        }
    } is sat

    specificWellFormedGameTest: {
        all g: Game | all t1: Team | {
            wellFormedGame[g]
            g.homeScore = 5
            g.awayScore = 2
            g.possession = t1
            g.playerWithBall = t1.pg
            g.time = 4
        }
    } is sat

    specificWellFormedGameTest_unsat: {
        some g: Game | some t1: Team | {
            wellFormedGame[g]
            g.homeScore = 0
            g.awayScore = 0
            g.possession = t1
            g.playerWithBall = t1.pg
            g.time = -1
        }
    } is unsat

    specificWellFormedPlayersTest: {
        all g: Game | all t1: Team | {
            wellFormedGame[g]
            g.homeScore = 0
            g.awayScore = 0
            g.possession = t1
            t1.pg.fgPercentage = 5
            t1.pg.threePointPercentage = 5
            t1.pg.reboundPercentage = 5
            g.playerWithBall = t1.pg
            g.time = 7
        }
    } is sat
}
