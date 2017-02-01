package exc;

import model.Board;

public class TowerAlreadyFullException extends IllegalCoordinatesException {
	private static final long serialVersionUID = 2L;
	private int x;
	private int y;
	private int zDim;
	
	/**
	 * Creates a new Tower Already Full Exception.
	 * @param x X coordinate of the tower.
	 * @param y Y coordinate of the tower.
	 * @param board board the tower is on.
	 */
	public TowerAlreadyFullException(int x, int y, Board board) {
		this.x = x;
		this.y = y;
		this.zDim = board.zDim;
	}

	/**
	 * Returns the message of the exception.
	 * @return String containing the message of the exception.
	 */
	@Override
	public String getMessage() { 
		return "Attempted to add a piece to the tower at (" + x + ", " + y + "), where all " +
				zDim + "cells are already occupied";
	}
}
