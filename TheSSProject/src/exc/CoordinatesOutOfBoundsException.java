package exc;

import model.Board;

public class CoordinatesOutOfBoundsException extends IllegalCoordinatesException {
	private static final long serialVersionUID = 1L;
	private int x;
	private int y;
	private int z = -1;
	private int xDim;
	private int yDim;
	private int zDim;
	
	/**
	 * Creates a new Coordinates out of bound Exception.
	 * @param x X coordinate
	 * @param y Y coordinate
	 * @param board Board on which the exception occurs.
	 */
	public CoordinatesOutOfBoundsException(int x, int y, Board board) {
		this.x = x;
		this.y = y;
		this.xDim = board.xDim;
		this.yDim = board.yDim;
	}
	
	/**
	 * Creates a new Coordinates out of bound Exception.
	 * @param x X coordinate
	 * @param y Y coordinate
	 * @param z Z coordinate
	 * @param board Board on which the exception occurs.
	 */
	public CoordinatesOutOfBoundsException(int x, int y, int z, Board board) {
		this.x = x;
		this.y = y;
		this.z = z;
		this.xDim = board.xDim;
		this.yDim = board.yDim;
		this.zDim = board.zDim;
	}
	
	/**
	 * Returns the message of the exception.
	 * @return String containing the message of the exception.
	 */
	@Override
	public String getMessage() {
		if (z == -1) {
			return "Tower coordinates larger than board dimensions. Got (" + x + ", " + y + 
					"), dimensions (" + xDim + ", " + yDim + ").";
		} else if (zDim == Board.UNLIMITED_Z) {
			return "Cell coordinates larger than board dimensions. Got (" + x + ", " + y + ", " + z
					+ "), dimensions (" + xDim + ", " + yDim + ", Inf).";
		} else {
			return "Cell coordinates larger than board dimensions. Got (" + x + ", " + y + ", " + z
					+ "), dimensions (" + xDim + ", " + yDim + ", " + zDim + ").";
		}
	}
}