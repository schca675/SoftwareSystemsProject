package model;

import java.util.List;

import exc.IllegalCoordinatesException;

public class SmartStrategy implements Strategy {

	// <------ Queries ------>
	@Override
	public String getName() {
		return "Trams";
	}

	//@ requires board != null && id > 0;
	@Override
	public TowerCoordinates determineMove(Board board, int id) {
		List<TowerCoordinates> availableTowers = board.getAvailableTowers();
		TowerCoordinates choice = null;
		int i = 0;
		
		//checking if I can win with the next move;
		while (choice == null && i < availableTowers.size()) {
			Board testBoard = board.deepCopy();
			TowerCoordinates test = availableTowers.get(i);
			int x = test.getX();
			int y = test.getY();
			try {
				testBoard.makeMove(x, y, id);
				if (testBoard.hasWon(x, y)) {
					choice = test;
				}
			} catch (IllegalCoordinatesException e) {
				//Should not be happening because the available Towers are determined 
				// and checked by the board. So do nothing.
			}
			i++;
		}

		if (choice != null) {
			return choice;
		} else {
			Strategy randi = new RandomStrategy();
			return randi.determineMove(board, id);
		}		
	}

}
