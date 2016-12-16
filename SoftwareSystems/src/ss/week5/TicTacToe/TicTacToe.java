package ss.week5.TicTacToe;

import ss.week5.ComputerPlayer;
import ss.week5.NaiveStrategy;
import ss.week5.Strategy;

/**
 * Executable class for the game Tic Tac Toe. The game can be played against the
 * computer. Lab assignment Module 2
 * 
 * @author Theo Ruys
 * @version $Revision: 1.4 $
 */
public class TicTacToe {
    public static void main(String[]args) {
        Player player1 = new HumanPlayer(args[0], Mark.OO);
        Strategy strategy;
        Player player2;
        if (args[1].equals("-N")) {
        	strategy = new NaiveStrategy();
            player2 = new ComputerPlayer(Mark.XX, strategy);
        } else {
        	player2 = new HumanPlayer(args[1], Mark.XX);
        }
        Game game = new Game(player1, player2);
        game.start();   
    }
}