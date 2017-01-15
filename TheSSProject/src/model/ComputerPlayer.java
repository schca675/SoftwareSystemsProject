package model;

public class ComputerPlayer extends Player {
	
	// <------ Instance variables ------>	
	
	Strategy strategy;

	// <------ Constructors ------>
	
	/**
	 * Creates a new computer player with given strategy and player ID.
	 * It gets the name of the strategy.
	 * @param strategy Strategy the computer Player plays with
	 * @param id Player ID the computer Player gets
	 */
	//@ requires strategy != null;
	//@ requires id>=0;
	public ComputerPlayer(Strategy strategy, int id) {
		super(strategy.getName(), id);
		this.strategy = strategy;
	}
	
	/**
	 * Creates a new computer player with the strategy "Random" and given player ID.
	 * @param id Player ID the computer Player gets
	 */
	//@ requires id >=0;
	public ComputerPlayer(int id) {
		super("Randi", id);
		this.strategy = new RandomStrategy();
	}
	
	// <------ Queries ------>
	
	/**
	 * Determines the coordinates of the tower for the next move.
	 * 
	 * @param board current board the game is played on.
	 * @return Coordinates of the tower for the next move.
	 */
	//@ requires board != null && !board.isFull();
	//@ ensures board.checkMove(\result.getX(),\result.getY());
	
	public TowerCoordinates determineMove(Board board) {
		return strategy.determineMove(board, this.playerID);
	}

}
