package model;

import java.util.List;
import java.util.Random;

import exc.TowerCoordinates;

public class RandomStrategy implements Strategy {

	// <------ Queries ------>
	
	@Override
	public String getName() {
		return "Randi";
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
		List<TowerCoordinates> availableTowers = board.getAvailableTowers();
		Random random = new Random();
		return availableTowers.get(random.nextInt(availableTowers.size()));
	}

}
