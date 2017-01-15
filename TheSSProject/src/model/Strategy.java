package model;

public interface Strategy {
	/**
	 * Get the name of the strategy.
	 * @return name of the strategy
	 */
	public String getName();
	
	/**
	 * Determining the next move by this strategy.
	 * @param board Board the game is played on.
	 * @param id player ID of the player using this strategy
	 * @return the index of the next move following this strategy
	 */
	//@ requires board != null && id !=null;
	//@ requires id == PlayerID.X || id == PlayerID.O;
	//@ ensures board.checkMove(\result.getX(),\result.getY());
	public TowerCoordinates determineMove(Board board, PlayerID id);

}
