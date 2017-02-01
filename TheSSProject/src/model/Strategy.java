package model;

public interface Strategy {
	
	// <------ Queries ------>
	/**
	 * Get the name of the strategy.
	 * @return name of the strategy
	 */
	public String getName();
	
	/**
	 * Determining the next move by this strategy.
	 * @param board Board the game is played on.
	 * @param id player ID of the player using this strategy.
	 * @return the coordinates of the next move following this strategy.
	 */
	//@ requires board != null;
	//@ requires id >=0;
	//@ ensures board.isValidMove(\result.getX(),\result.getY());
	public TowerCoordinates determineMove(Board board, int id);

}
