package ss.week5.TicTacToe;

import ss.week5.ComputerPlayer;
import ss.week5.NaiveStrategy;
import ss.week5.SmartStrategy;
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
        Player[] players = new Player[2];
        Strategy strategy;
        Mark mark = Mark.OO;
        for (int i = 0; i < players.length; i++) {
        	// Determing if the computer plays
        	if (args[i].equals("-N")) {
            	strategy = new NaiveStrategy();
        	} else if (args[i].equals("-S")) {
            	strategy = new SmartStrategy();
        	} else {
        		strategy = null;
        	}
        	// If a player has a strategy, he is a computer, else he is human.
        	if (strategy != null) {
        		players[i] = new ComputerPlayer(mark, strategy);
        	} else {
        		players[i] = new HumanPlayer(args[i], mark);
        	}
        	mark = mark.other();
        }
        Game game = new Game(players[0], players[1]);
        game.start();   
    }
    
    
/*public class TicTacToe {
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
    }    */
	    
}