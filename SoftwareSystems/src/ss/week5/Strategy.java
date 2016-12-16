package ss.week5;

import ss.week5.TicTacToe.Board;
import ss.week5.TicTacToe.Mark;

public interface Strategy {
	public String getName();
	
	public int determineMove(Board b, Mark m);
}
