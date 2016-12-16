package ss.week5;

import ss.week5.TicTacToe.Board;
import ss.week5.TicTacToe.Mark;
import ss.week5.TicTacToe.Player;

public class ComputerPlayer extends Player {
	Strategy strategy;
	
	public ComputerPlayer(Mark mark, Strategy strategy) {
		super(strategy.getName() + "-" + mark.toString(), mark);
		this.strategy = strategy;
	}
	
	public ComputerPlayer(Mark mark) {
		super("Naive-" + mark.toString(), mark);
		this.strategy = new NaiveStrategy();
	}

	@Override
	public int determineMove(Board board) {
		return strategy.determineMove(board, this.getMark());
	}

}
