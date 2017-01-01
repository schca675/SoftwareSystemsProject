package model;

import java.util.ArrayList;
import java.util.List;

public class Board<PLAYERIDTYPE> {
	
	// <------ Constants ------>
	
	public static final int DEFAULT_XDIM = 4;
	public static final int DEFAULT_YDIM = 4;
	public static final int DEFAULT_ZDIM = 4;
	public static final int DEFAULT_WIN = 4;
	public static final int UNLIMITED_Z = -1;
	
	// <------ Instance variables ------>
	
	private int xDim;
	private int yDim;
	private int zDim;
	private int winningLength;
	private List<List<PLAYERIDTYPE>> boardData;
	
	// <------ Constructors ------>
	
	/** Create a new board with specified dimensions and winning length.
	 * @param xDim X dimension of the board
	 * @param yDim Y dimension of the board
	 * @param zDim Z dimension of the board, -1 specifies unlimited
	 * @param winningLength Connected pieces required to win the game
	 */
	/*@ requires winningLength <= xDim || winningLength <= yDim 
	  @ || (zDim > 0 && winningLength <= zDim) || (zDim == UNLIMITED_Z);
	*/
	//@ requires xDim > 0 && yDim > 0 && (zDim > 0 || zDim == -1) && winningLength > 0;
	public Board(int xDim, int yDim, int zDim, int winningLength) {
		this.xDim = xDim;
		this.yDim = yDim;
		this.zDim = zDim;
		this.winningLength = winningLength;
		reset();
	}
	
	/** Create a board with default settings and rules.
	 * 
	 */
	public Board() {
		this(DEFAULT_XDIM, DEFAULT_YDIM, DEFAULT_ZDIM, DEFAULT_WIN);
	}
	
	
	// <------ Queries ------>
	
	/** Getter for X dimension.
	 * 
	 * @return X dimension
	 */
	/*@ pure */ public int getXDim() {
		return xDim;
	}

	/** Getter for Y dimension.
	 * 
	 * @return Y dimension
	 */
	/*@ pure */ public int getYDim() {
		return yDim;
	}

	/** Getter for Z dimension.
	 * 
	 * @return Z dimension
	 */
	/*@ pure */ public int getZDim() {
		return zDim;
	}
	
	/** Gets the tower at (x,y), assuming there is one.
	 * 
	 * @param x X position
	 * @param y Y position
	 * @return Tower at (x,y)
	 */
	//@ requires isValidTower(x,y);
	/*@ pure */ public List<PLAYERIDTYPE> getTower(int x, int y) {
		return boardData.get((x - 1) + (y - 1) * yDim);
	}
	
	/** Checks whether a piece can be added at (x,y).
	 * 
	 * @param x X position to check
	 * @param y Y position to check
	 * @return Tower at (x,y) exists and isn't full
	 */
	//@ ensures getZDim() == -1 ==> \result == (isValidTower(x,y));
	//@ ensures getZDim() > 0 ==> \result == (isValidTower(x,y) && getTowerHeight(x,y) < getZDim());
	/*@ pure */ public boolean checkMove(int x, int y) {
		if (zDim == UNLIMITED_Z) {
			return isValidTower(x, y);
		} else {
			return isValidTower(x, y) && getTowerHeight(x, y) < getZDim();
		}
	}
	
	/** Returns the owner of the (assumed valid) cell (x,y,z), null if no owner.
	 * 
	 * @param x X position
	 * @param y Y position
	 * @param z Z position
	 * @return Owner, null if no owner
	 */
	//@ requires isValidCell(x,y,z);
	//TODO: Determine PLAYERIDTYPE --> PlayerID
	// ensures \result == null || \result instanceof PLAYERIDTYPE;
	/*@ pure nullable */ public PLAYERIDTYPE getCellOwner(int x, int y, int z) {
		if (z <= getTowerHeight(x, y)) {
			return getTower(x, y).get(z - 1);
		} else {
			return null;
		}
	}
	/** Checks whether the given cell is empty.
	 * 
	 * @param x X position to check
	 * @param y Y position to check
	 * @param z Z position to check
	 * @return (x,y,z) is empty
	 */
	//@ requires isValidCell(x,y,z);
	//@ ensures \result == (getCellOwner(x,y,z) == null);
	/*@ pure */ public boolean isEmptyCell(int x, int y, int z) {
		return getCellOwner(x, y, z) == null;
	}
	
	/** Checks whether the board is full.
	 * 
	 * @return Board is full
	 */
	//@ ensures \result == (\forall int x,y,z; isValidCell(x,y,z); !isEmptyCell(x,y,z));
	/*@ pure */ public boolean isFull() {
		if (zDim == UNLIMITED_Z) {
			return false;
		} else {
			for (List<PLAYERIDTYPE> tower : boardData) {
				if (tower.size() < zDim) {
					return false;
				}
			}
			return true;
		}
	}
	
	/** Returns the height of the tower at (x,y).
	 * 
	 * @param x X position to check
	 * @param y Y position to check
	 * @return The height of the tower at (x,y)
	 */
	//@ requires isValidTower(x,y);
	// ensures \result == ?;
	/*@ pure */ public int getTowerHeight(int x, int y) {
		return getTower(x, y).size();
	}
	
	/** Checks whether the piece at (x,y,z) belongs to a winning set.
	 * 
	 * @param x X position to check
	 * @param y Y position to check
	 * @param z Z position to check
	 * @return Piece at (x,y,z) belongs to winning set
	 */
	//@ requires isValidCell(x,y,z) && !isEmptyCell(x,y,z);
	/*@ pure */ public boolean hasWon(int x, int y, int z) {
		// Linearly independent direction vectors:
		// (1,0,0) X-direction
		// (0,1,0) Y-direction
		// (0,0,1) Z-direction
		// (1,1,0) X+Y-direction
		// (1,-1,0) X-Y-direction
		// (1,0,1) X+Z-direction
		// (1,0,-1) X-Z-direction
		// (0,1,1) Y+Z-direction
		// (0,1,-1) Y-Z-direction
		// (1,1,1) X+Y+Z-direction
		// (1,1,-1) X+Y-Z-direction
		// (1,-1,1) X-Y+Z-direction
		// (1,-1,-1) X-Y-Z-direction
		return directionHasWon(x, y, z, 1, 0, 0) || 
				directionHasWon(x, y, z, 0, 1, 0) || 
				directionHasWon(x, y, z, 0, 0, 1) || 
				directionHasWon(x, y, z, 1, 1, 0) ||
				directionHasWon(x, y, z, 1, -1, 0) || 
				directionHasWon(x, y, z, 1, 0, 1) ||
				directionHasWon(x, y, z, 1, 0, -1) || 
				directionHasWon(x, y, z, 0, 1, 1) ||
				directionHasWon(x, y, z, 0, 1, -1) || 
				directionHasWon(x, y, z, 1, 1, 1) ||
				directionHasWon(x, y, z, 1, 1, -1) || 
				directionHasWon(x, y, z, 1, -1, 1) ||
				directionHasWon(x, y, z, 1, -1, -1);
	}
	
	//Check JML & Javadoc.
	
	/** Checks whether the direction (deltax,deltay,deltaz) 
	 * belonging to the cell (x,y,z) is winning. 
	 * 
	 * @param x X position to check
	 * @param y Y position to check
	 * @param z Z position to check
	 * @param deltax
	 * @param deltay
	 * @param deltaz
	 * @return if the direction is winning.
	 */
	//@ requires isValidCell(x,y,z) && !isEmptyCell(x,y,z);
	/*@ pure */ private boolean directionHasWon(int x, int y, int z, 
													int deltax, int deltay, int deltaz) {
		int connectedPieces = 1;
		PLAYERIDTYPE owner = getCellOwner(x, y, z);
		int distance = 1;
		int sign = 1;
		while (connectedPieces < winningLength) {
			int checkX = x + sign * distance * deltax;
			int checkY = y + sign * distance * deltay;
			int checkZ = z + sign * distance * deltaz;
			if (isValidCell(checkX, checkY, checkZ) && getCellOwner(checkX, checkY, checkZ) != null
					&& getCellOwner(checkX, checkY, checkZ).equals(owner)) {
				connectedPieces = connectedPieces + 1;
				distance = distance + 1;
			} else {
				if (sign == 1) {
					//Reverse
					sign = -1;
					distance = 1;
				} else {
					//If reversed already, terminate
					return false;
				}
			}
		}
		return true;
	}
	
	/** Checks whether (x,y) is a valid tower on the board.
	 * 
	 * @param x X position
	 * @param y Y position
	 * @return (x,y) are valid coordinates on the board
	 */
	//@ ensures \result == (x > 0 && x <= getXDim() && y > 0 && y <= getYDim());
	/*@ pure */ public boolean isValidTower(int x, int y) {
		return x > 0 && x <= xDim && y > 0 && y <= yDim;
	}
	
	/** Checks whether (x,y,z) is a valid cell on the board.
	 * 
	 * @param x X position
	 * @param y Y position
	 * @param z Z position
	 * @return (x,y,z) are valid coordinates on the board
	 */
	//@ ensures \result == (isValidTower(x,y) && z > 0 && z <= getZDim());
	/*@ pure */ public boolean isValidCell(int x, int y, int z) {
		if (zDim == UNLIMITED_Z) {
			return isValidTower(x, y);
		} else {
			return isValidTower(x, y) && z > 0 && z <= zDim;
		}
	}
	
	
	// <------ Commands ------>
	
	/** Make a move, assumes checkMove(x,y) has been called.
	 * 
	 * @param x X position to place piece at
	 * @param y Y position to place piece at
	 * @param playerID ID of player that makes a move
	 */
	//@ requires checkMove(x,y);
	//@ ensures getCellOwner(x,y,getTowerHeight(x,y)) == playerID;
	public void makeMove(int x, int y, PLAYERIDTYPE playerID) {
		getTower(x, y).add(playerID);
	}
	
	/** Resets the board to an empty board.
	 * 
	 */
	//@ ensures \forall int x,y,z; isValidCell(x,y,z); isEmptyCell(x,y,z);
	private void reset() {
		boardData = new ArrayList<List<PLAYERIDTYPE>>();
		// More efficient way to do this?
		for (int i = 0; i < xDim * yDim; i++) {
			boardData.add(new ArrayList<PLAYERIDTYPE>());
		}
	}
}
