#lang forge/bsl

// *****************************************************DEFINITONS*****************************************************
// each posiition/player has statistics that determines they skills/playstyle
abstract sig Position {
    fgPercentage: one Int,
    threePointPercentage: one Int,
    reboundPercentage: one Int

    // possibly add more states, rules, and fouls in future iterations
    // ftPercentage: one Int,
    // assistPercentage: one Int
}

// positions we model
// limiting to 3 players per team to help with graph visibility and understanding
// models how a typical basketball has these defined positions
sig PG extends Position {}
sig SG extends Position {}
sig C extends Position {}

// models a team with 3 players
sig Team {
    pg: one PG,
    sg: one SG,
    c: one C
}

// models a game with a typical away and home team
// ensures that only two teams are playing and that they are different
// cannot have one team or three teams
one sig HomeTeam extends Team {}
one sig AwayTeam extends Team {}

abstract sig Bool {}
one sig True extends Bool {}
one sig False extends Bool {}

// models a game with a score, time, and possession
sig Game {
    homeScore: one Int,
    awayScore: one Int,
    possession: one Team,
    playerWithBall: one Position,
    time: one Int,
    next: lone Game
    --isFoul: one Bool,
    --isShootingFoul: one Bool

    // other considerations
    // homeFouls: one Int,
    // awayFouls: one Int,
}

// ********************************************************************************************************************
// *****************************************************WELLFORMED*****************************************************


pred negstatg[g: Game] {
    g.homeScore < 0 or
    g.awayScore < 0 or
    g.time < 0 
}

pred nonnegstatg[g: Game] {
    not negstatg[g]
}

// defines a well formed game that enforces the sigs created above
// as wel as logical constraints
pred wellFormedGame[g: Game] {
    g.homeScore >= 0
    g.awayScore >= 0
    g.possession = HomeTeam or g.possession = AwayTeam
    g.time >= 0
    HomeTeam.pg != AwayTeam.pg
    HomeTeam.pg.reboundPercentage >= 0
    AwayTeam.pg.reboundPercentage >= 0
    HomeTeam.sg != AwayTeam.sg
    HomeTeam.sg.reboundPercentage >= 0
    AwayTeam.sg.reboundPercentage >= 0
    HomeTeam.c != AwayTeam.c
    HomeTeam.c.reboundPercentage >= 0
    AwayTeam.c.reboundPercentage >= 0

    // added possession and player with ball complexity
    g.possession = HomeTeam => g.playerWithBall = HomeTeam.pg or g.playerWithBall = HomeTeam.sg or g.playerWithBall = HomeTeam.c
    g.possession = AwayTeam => g.playerWithBall = AwayTeam.pg or g.playerWithBall = AwayTeam.sg or g.playerWithBall = AwayTeam.c
    
    // added foul complexity
    -- g.isFoul = True or g.isFoul = False
    -- g.isShootingFoul = True or g.isShootingFoul = False


    // must follow linearity of time
    // therefore, even if none of the fields are changed
    // time must be decremented by 1
    not reachable[g, g, next]
}

pred wellFormedPlayers[g: Game] {
    HomeTeam.pg != AwayTeam.pg
    HomeTeam.pg.reboundPercentage >= 0
    AwayTeam.pg.reboundPercentage >= 0
    HomeTeam.sg != AwayTeam.sg
    HomeTeam.sg.reboundPercentage >= 0
    AwayTeam.sg.reboundPercentage >= 0
    HomeTeam.c != AwayTeam.c
    HomeTeam.c.reboundPercentage >= 0
    AwayTeam.c.reboundPercentage >= 0
}

pred wellFormedPossession[g: Game] {
    g.possession = HomeTeam or g.possession = AwayTeam
    g.possession = HomeTeam => g.playerWithBall = HomeTeam.pg or g.playerWithBall = HomeTeam.sg or g.playerWithBall = HomeTeam.c
    g.possession = AwayTeam => g.playerWithBall = AwayTeam.pg or g.playerWithBall = AwayTeam.sg or g.playerWithBall = AwayTeam.c
}

pred wellFormedScoreAndTime[g: Game] {
    g.homeScore >= 0
    g.awayScore >= 0
    g.time >= 0
}

pred notWellFormed[g: Game] {
    not wellFormedGame[g]
}

// **************************************************************************************************************
// *****************************************************INIT*****************************************************
// defines a well formed initial start of a game
pred init[game: Game] {
    HomeTeam != AwayTeam
    game.homeScore = 0
    game.awayScore = 0

    // attempts to model tip off, but not perfect
    (HomeTeam.c.reboundPercentage > AwayTeam.c.reboundPercentage) => {
        game.possession = HomeTeam
        game.playerWithBall = HomeTeam.c
        or
        game.playerWithBall = HomeTeam.pg
        or
        game.playerWithBall = HomeTeam.sg
    }
    (HomeTeam.c.reboundPercentage < AwayTeam.c.reboundPercentage) => {
        game.possession = AwayTeam
        game.playerWithBall = AwayTeam.c
        or
        game.playerWithBall = AwayTeam.pg
        or
        game.playerWithBall = AwayTeam.sg
    }
    game.time = 7
    --game.isFoul = False
    --game.isShootingFoul = False

    // extra check, must be true
    wellFormedGame[game]
}
// *******************************************************************************************************************
// *****************************************************WIN_CONDITIONS************************************************
// checks for no winner
// either one no winner or a tie
pred nowinner[g: Game] {
    g.time = 0
    not winner[g]
}

// checks for a winner
pred winner[game: Game] {
    game.time = 0
    game.homeScore > game.awayScore or game.awayScore > game.homeScore
}

// checks for a tie
pred notie[g: Game] {
    g.time = 0
    not tie[g]
}

// checks for no tie
pred tie[game: Game] {
    game.time = 0
    game.homeScore = game.awayScore
}

// checks for odd score
pred oddScore[gameState1, gameState2: Game] {
    subtract[gameState2.homeScore, gameState1.homeScore] = 1 or
    subtract[gameState2.homeScore, gameState1.homeScore] > 3 or

    subtract[gameState2.awayScore, gameState1.awayScore] = 1 or
    subtract[gameState2.awayScore, gameState1.awayScore] > 3 
}

// checks for even score
pred notOddScore[gameState1, gameState2: Game] {
    not oddScore[gameState1, gameState2]
}

// checks for valid score
pred validScore[g: Game] {
    g.homeScore >= 0 and g.homeScore != 1 
    g.awayScore >= 0 and g.awayScore != 1 
}

// *****************************************************************************************************************
// *****************************************************SCORING*****************************************************
pred nextValidTimeAndScore[gameState1, gameState2: Game] {
    gameState1.next = gameState2
    gameState2.time = subtract[gameState1.time, 1]

    gameState2.homeScore >= gameState1.homeScore
    gameState2.awayScore >= gameState1.awayScore
}

pred nextValidScoring[gameState1, gameState2: Game] {
    (add[HomeTeam.pg.reboundPercentage, add[HomeTeam.sg.reboundPercentage, HomeTeam.c.reboundPercentage]] >
    add[AwayTeam.pg.reboundPercentage, add[AwayTeam.sg.reboundPercentage, AwayTeam.c.reboundPercentage]]) =>
    gameState2.possession = HomeTeam else gameState2.possession = AwayTeam
    
    gameState2.possession = AwayTeam => {
        gameState1.playerWithBall = HomeTeam.pg => {
            add[HomeTeam.pg.fgPercentage, 1] > HomeTeam.pg.threePointPercentage => {
                gameState2.homeScore = add[gameState1.homeScore, 2]
                or 
                gameState2.homeScore = gameState1.homeScore
            }
            add[HomeTeam.pg.fgPercentage, 1] < HomeTeam.pg.threePointPercentage => {
                gameState2.homeScore = add[gameState1.homeScore, 3]
                or 
                gameState2.homeScore = gameState1.homeScore
            }
        }
        gameState1.playerWithBall = HomeTeam.sg => {
            add[HomeTeam.sg.fgPercentage, 1] > HomeTeam.sg.threePointPercentage => {
                gameState2.homeScore = add[gameState1.homeScore, 2]
                or 
                gameState2.homeScore = gameState1.homeScore
            }
            add[HomeTeam.sg.fgPercentage, 1] < HomeTeam.sg.threePointPercentage => {
                gameState2.homeScore = add[gameState1.homeScore, 3]
                or 
                gameState2.homeScore = gameState1.homeScore
            }
        }
        gameState1.playerWithBall = HomeTeam.c => {
            add[HomeTeam.c.fgPercentage, 1] > HomeTeam.c.threePointPercentage => {
                gameState2.homeScore = add[gameState1.homeScore, 2]
                or 
                gameState2.homeScore = gameState1.homeScore
            }
            add[HomeTeam.c.fgPercentage, 1] < HomeTeam.c.threePointPercentage => {
                gameState2.homeScore = add[gameState1.homeScore, 3]
                or 
                gameState2.homeScore = gameState1.homeScore
            }
        }
        
    }
    gameState2.possession = HomeTeam => {
        // same logic as above
        gameState1.playerWithBall = AwayTeam.pg => {
            add[AwayTeam.pg.fgPercentage, 1] > AwayTeam.pg.threePointPercentage => {
                gameState2.awayScore = add[gameState1.awayScore, 2]
                or 
                gameState2.awayScore = gameState1.awayScore
            }
            add[AwayTeam.pg.fgPercentage, 1] < AwayTeam.pg.threePointPercentage => {
                gameState2.awayScore = add[gameState1.awayScore, 3]
                or 
                gameState2.awayScore = gameState1.awayScore
            }
        }

        gameState1.playerWithBall = AwayTeam.sg => {
            add[AwayTeam.sg.fgPercentage, 1] > AwayTeam.sg.threePointPercentage => {
                gameState2.awayScore = add[gameState1.awayScore, 2]
                or 
                gameState2.awayScore = gameState1.awayScore
            }
            add[AwayTeam.sg.fgPercentage, 1] < AwayTeam.sg.threePointPercentage => {
                gameState2.awayScore = add[gameState1.awayScore, 3]
                or 
                gameState2.awayScore = gameState1.awayScore
            }
        }

        gameState1.playerWithBall = AwayTeam.c => {
            add[AwayTeam.c.fgPercentage, 1] > AwayTeam.c.threePointPercentage => {
                gameState2.awayScore = add[gameState1.awayScore, 2]
                or 
                gameState2.awayScore = gameState1.awayScore
            }
            add[AwayTeam.c.fgPercentage, 1] < AwayTeam.c.threePointPercentage => {
                gameState2.awayScore = add[gameState1.awayScore, 3]
                or 
                gameState2.awayScore = gameState1.awayScore
            }
        }
    
    }

    subtract[gameState2.homeScore, gameState1.homeScore] = 2 or
    subtract[gameState2.homeScore, gameState1.homeScore] = 3 or
    subtract[gameState2.homeScore, gameState1.homeScore] = 0

    subtract[gameState2.awayScore, gameState1.awayScore] = 2 or
    subtract[gameState2.awayScore, gameState1.awayScore] = 3 or
    subtract[gameState2.awayScore, gameState1.awayScore] = 0
}

pred nextPossession[gameState1, gameState2: Game] {
    // make sure the game states are well formed
    wellFormedGame[gameState1]
    wellFormedGame[gameState2]

    // make sure the game states are not the same
    // and that the time is decremented by 1
    gameState1.next = gameState2
    gameState2.time = subtract[gameState1.time, 1]

    // make sure that the scores are valid
    // cannot lose points
    gameState2.homeScore >= gameState1.homeScore
    gameState2.awayScore >= gameState1.awayScore

    // we could add foul logic here but it would be very complex and hard to read
    // although we get a result, it is untested.
    // gameState1.isFoul = True => {
    //     gameState2.isFoul = False
    //     // if a foul is called, the team that was fouled will have possession
    //     gameState1.possession = HomeTeam => gameState2.possession = HomeTeam
    //     gameState1.possession = AwayTeam => gameState2.possession = AwayTeam
    //     }

    // gameState1.isShootingFoul = True => {
    //     gameState2.isShootingFoul = False
    //     // if a shooting foul is called, score 0, 1, 2 points
    //     gameState1.possession = HomeTeam => gameState2.possession = AwayTeam
    //     gameState1.possession = AwayTeam => gameState2.possession = HomeTeam

    //     gameState1.possession = HomeTeam => {
    //         gameState2.awayScore = gameState1.awayScore
    //         gameState2.homeScore = add[gameState1.homeScore, 1] or
    //         gameState2.homeScore = add[gameState1.homeScore, 2] or
    //         gameState2.homeScore = gameState1.homeScore
    //     }

    //     gameState1.possession = AwayTeam => {
    //         gameState2.homeScore = gameState1.homeScore
    //         gameState2.awayScore = add[gameState1.awayScore, 1] or
    //         gameState2.awayScore = add[gameState1.awayScore, 2] or
    //         gameState2.awayScore = gameState1.awayScore
    //     }
    // }

    --(gameState1.isFoul = False and gameState1.isShootingFoul = False) => { 
    --    gameState2.isFoul = True or gameState2.isShootingFoul = True
    --    gameState2.isFoul = False or gameState2.isShootingFoul = False
    -- rest of code below

    // attempts to introduce rebounding and possession
    // if the overall rebounding percentage is higher, they should have possession
    // would want to use probability here but not possible
    // otherwise, in a more basic model, we have something like
    -- gameState1.possession = HomeTeam => gameState2.possession = AwayTeam
    -- gameState1.possession = AwayTeam => gameState2.possession = HomeTeam


    (add[HomeTeam.pg.reboundPercentage, add[HomeTeam.sg.reboundPercentage, HomeTeam.c.reboundPercentage]] >
    add[AwayTeam.pg.reboundPercentage, add[AwayTeam.sg.reboundPercentage, AwayTeam.c.reboundPercentage]]) =>
    gameState2.possession = HomeTeam else gameState2.possession = AwayTeam
    
    gameState2.possession = AwayTeam => {
        // in the most basic model, we either score 2 or 3 or 0 points
        --gameState1.possession = HomeTeam
        --gameState2.awayScore = gameState1.awayScore
        --(gameState2.homeScore = add[gameState1.homeScore, 2] 
        --or
        --gameState2.homeScore = add[gameState1.homeScore, 3]
        --or 
        --gameState2.homeScore = add[gameState1.homeScore, 1]
        --or
        --gameState2.homeScore = gameState1.homeScore)

        // to introduce player statistics more, we attempt to model how
        // players will play to their strengths. For example, if the point guard
        // has a higher field goal percentage than three point percentage, they will
        // attempt to score 2 points and vice versa
        // The or is used to model the possibility of missing the shot
        
        // added complexity of who has the balls and their position
        // check the point guard, shooting guard, and center
        gameState1.playerWithBall = HomeTeam.pg => {
            HomeTeam.pg.fgPercentage > HomeTeam.pg.threePointPercentage => {
                gameState2.homeScore = add[gameState1.homeScore, 2]
                or 
                gameState2.homeScore = gameState1.homeScore
            }
            HomeTeam.pg.fgPercentage < HomeTeam.pg.threePointPercentage => {
                gameState2.homeScore = add[gameState1.homeScore, 3]
                or 
                gameState2.homeScore = gameState1.homeScore
            }
        }
        gameState1.playerWithBall = HomeTeam.sg => {
            HomeTeam.sg.fgPercentage > HomeTeam.sg.threePointPercentage => {
                gameState2.homeScore = add[gameState1.homeScore, 2]
                or 
                gameState2.homeScore = gameState1.homeScore
            }
            HomeTeam.sg.fgPercentage < HomeTeam.sg.threePointPercentage => {
                gameState2.homeScore = add[gameState1.homeScore, 3]
                or 
                gameState2.homeScore = gameState1.homeScore
            }
        }
        gameState1.playerWithBall = HomeTeam.c => {
            HomeTeam.c.fgPercentage > HomeTeam.c.threePointPercentage => {
                gameState2.homeScore = add[gameState1.homeScore, 2]
                or 
                gameState2.homeScore = gameState1.homeScore
            }
            HomeTeam.c.fgPercentage < HomeTeam.c.threePointPercentage => {
                gameState2.homeScore = add[gameState1.homeScore, 3]
                or 
                gameState2.homeScore = gameState1.homeScore
            }
        }
        
    }
    gameState2.possession = HomeTeam => {
        // same logic as above
        gameState1.playerWithBall = AwayTeam.pg => {
            AwayTeam.pg.fgPercentage > AwayTeam.pg.threePointPercentage => {
                gameState2.awayScore = add[gameState1.awayScore, 2]
                or 
                gameState2.awayScore = gameState1.awayScore
            }
            AwayTeam.pg.fgPercentage < AwayTeam.pg.threePointPercentage => {
                gameState2.awayScore = add[gameState1.awayScore, 3]
                or 
                gameState2.awayScore = gameState1.awayScore
            }
        }

        gameState1.playerWithBall = AwayTeam.sg => {
            AwayTeam.sg.fgPercentage > AwayTeam.sg.threePointPercentage => {
                gameState2.awayScore = add[gameState1.awayScore, 2]
                or 
                gameState2.awayScore = gameState1.awayScore
            }
            AwayTeam.sg.fgPercentage < AwayTeam.sg.threePointPercentage => {
                gameState2.awayScore = add[gameState1.awayScore, 3]
                or 
                gameState2.awayScore = gameState1.awayScore
            }
        }

        gameState1.playerWithBall = AwayTeam.c => {
            AwayTeam.c.fgPercentage > AwayTeam.c.threePointPercentage => {
                gameState2.awayScore = add[gameState1.awayScore, 2]
                or 
                gameState2.awayScore = gameState1.awayScore
            }
            AwayTeam.c.fgPercentage < AwayTeam.c.threePointPercentage => {
                gameState2.awayScore = add[gameState1.awayScore, 3]
                or 
                gameState2.awayScore = gameState1.awayScore
            }
        }
    
    }
    // }

    subtract[gameState2.homeScore, gameState1.homeScore] = 2 or
    subtract[gameState2.homeScore, gameState1.homeScore] = 3 or
    subtract[gameState2.homeScore, gameState1.homeScore] = 0

    subtract[gameState2.awayScore, gameState1.awayScore] = 2 or
    subtract[gameState2.awayScore, gameState1.awayScore] = 3 or
    subtract[gameState2.awayScore, gameState1.awayScore] = 0

}

// *****************************************************RUNNING*****************************************************

// simple game
// run {
//     some g: Game | {
//         init[g]
//         wellFormedGame[g]
//     } 
// } for 5 Int, exactly 2 PG, exactly 2 SG, exactly 2 C, 5 Game for {next is linear}

// Two game transition
// run {
//     some g, g2: Game | {
//         init[g]
//         nextPossession[g, g2]
//         wellFormedGame[g2]
//     } 
// } for 5 Int, exactly 2 PG, exactly 2 SG, exactly 2 C, 2 Game for {next is linear}

// Two game transition with winner
// run {
//     some g, g2: Game | {
//         wellFormedGame[g]
//         nextPossession[g, g2]
//         wellFormedGame[g2]
//         winner[g2]
//     } 
// } for 5 Int, exactly 2 PG, exactly 2 SG, exactly 2 C, 2 Game for {next is linear}

// run {
//     all g: Game | {
//         wellFormedGame[g]
//     }
//     some disj g, g1, g2, g3, g4, g5, g6, g7: Game | {
//         init[g]
//         nextPossession[g, g1]
//         nextPossession[g1, g2]
//         nextPossession[g2, g3]
//         nextPossession[g3, g4]
//         nextPossession[g4, g5]
//         nextPossession[g5, g6]
//         nextPossession[g6, g7]
//         winner[g7]
//     } 
// } for 5 Int, exactly 2 PG, exactly 2 SG, exactly 2 C, 8 Game for {next is linear}

run {
    all g: Game | {
        wellFormedGame[g]
    }
    some disj g, g1, g7: Game | {
        init[g]
        nextPossession[g, g1]
        all g: Game | {
            some g.next implies {
                nextPossession[g, g.next]
                wellFormedGame[g.next]
            }
        }
        winner[g7]
    } 
} for 5 Int, exactly 2 PG, exactly 2 SG, exactly 2 C, 8 Game for {next is linear}
// *******************************************************************************************************************
