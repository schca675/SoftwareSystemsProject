package model;

public class TowerAlreadyFullException extends IllegalCoordinatesException {
	private static final long serialVersionUID = 2L;
	private int x;
	private int y;
	private int zDim;
	
	public TowerAlreadyFullException(int x, int y, Board board) {
		this.x = x;
		this.y = y;
		this.zDim = board.zDim;
	}

	@Override
	public String getMessage() { 
		return "Attempted to add a piece to the tower at (" + x + ", " + y + "), where all " +
				zDim + "cells are already occupied";
	}
}
