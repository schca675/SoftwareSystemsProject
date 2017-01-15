package model;

public class RandomStrategy implements Strategy {

	// <------ Queries ------>
	
	@Override
	public String getName() {
		return "Random strategy";
	}

	//To do 
	/**
	 * Determining the next move by choosing a random valid field.
	 * @param board Board the game is played on.
	 * @param id player ID of the player using this strategy
	 * @return the index of the next move following this strategy
	 */
	//@ requires board != null;
	//@ requires id >= 0;
	//@ ensures board.isValidMove(\result.getX(),\result.getY());
	@Override
	public TowerCoordinates determineMove(Board board, int id) {
		// TODO Auto-generated method stub
		return null;
	}

}
