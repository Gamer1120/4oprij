package server;

import game.Board;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;

/**
 * Server. A Thread class that listens to a socket connection on a specified
 * port. For every socket connection with a client, a new ClientHandler thread
 * is started.<br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */
public class Server extends Thread {
	// PROTOCOL
	public static final String ACCEPT_CONNECT = "OK";
	public static final String ERROR = "ERROR";
	public static final String LOBBY = "LOBBY";
	public static final String INVITE = "INVITE";
	public static final String DECLINE_INVITE = "DECLINE";
	public static final String GAME_START = "START";
	public static final String GAME_END = "END";
	public static final String REQUEST_MOVE = "REQUEST";
	public static final String MOVE_OK = "MOVE";
	public static final String BOARD = "BOARD";
	public static final String CHAT = "CHAT";
	public static final String LEADERBOARD = "LEADERBOARD";
	public static final String PONG = "PONG";
	// END OF PROTOCOL

	public static final String FEATURES = ClientHandler.CHAT + " "
			+ ClientHandler.LEADERBOARD + " " + ClientHandler.CUSTOM_BOARD_SIZE;
	public static final String FILENAME = "leaderboard.txt";

	/** The socket of the server. */
	private ServerSocket ss;

	/** The User Interface of the server. */
	private MessageUI mui;

	/** The set of all the clientHanlders connected to this server. */
	private HashSet<ClientHandler> threads;

	/**
	 * The map of invites with a String array with the name of the client who
	 * sent the invite and the name of the client who received the invite
	 * respectively, and with an Integer array with the boardsize.
	 */
	private HashMap<String[], Integer[]> invites;

	/**
	 * The leaderboard list, sorted using Collections.sort. The order is based
	 * on the natural ordering of LeaderboardPair.
	 */
	private ArrayList<LeaderboardPair> leaderboard;

	/*@ private invariant ss != null;
		private invariant mui != null;
		private invariant threads != null;
		private invariant invites != null;
		private invariant leaderboard != null;
	 */
	/**
	 * Constructs a new Server object. Tries to read the leaderboard, if the
	 * leaderboard file can't be read it creates a new leaderboard.
	 *
	 * @param portArg
	 *            the port of the server
	 * @param muiArg
	 *            the view of the server
	 * @throws IOException
	 *             if the server can't be created, most likely due too the port
	 *             being occupied
	 */
	/*@ requires portArg >= 1 & portArg <= 65535;
		requires muiArg != null;
	 */
	public Server(int portArg, MessageUI muiArg) throws IOException {
		this.ss = new ServerSocket(portArg);
		this.mui = muiArg;
		this.threads = new HashSet<ClientHandler>();
		this.invites = new HashMap<String[], Integer[]>();
		try {
			this.leaderboard = readLeaderboard();
			mui.addMessage("Read leaderboard.");
		} catch (IOException e) {
			this.leaderboard = new ArrayList<LeaderboardPair>();
			mui.addMessage("Created new leaderboard.");
		}
	}

	/**
	 * Listens to a port of this Server if there are any Clients that would like
	 * to connect. For every new socket connection a new ClientHandler thread is
	 * started that takes care of the further communication with the client.
	 */
	@Override
	public void run() {
		while (true) {
			try {
				Socket s = ss.accept();
				ClientHandler ch = new ClientHandler(this, s);
				addHandler(ch);
				ch.start();
			} catch (IOException e) {
				mui.addMessage("Error adding client.");
				continue;
			}
		}
	}

	/**
	 * Sends a message using the collection of connected ClientHandlers to all
	 * connected Clients.
	 * 
	 * @param msg
	 *            message that is send
	 */
	//@ requires msg != null;
	public void broadcast(String msg) {
		synchronized (threads) {
			mui.addMessage("Broadcast: " + msg);
			//@ loop_invariant threads.contains(ch);
			for (ClientHandler ch : threads) {
				if (ch.connected()) {
					ch.sendMessage(msg);
				}
			}
		}
	}

	/**
	 * Sends a message using the collection of connected ClientHandlers to all
	 * connected Clients without a game.
	 */
	public void broadcastLobby() {
		synchronized (threads) {
			String lobby = lobbyToString();
			mui.addMessage("Lobby:" + lobby);
			//@ loop_invariant threads.contains(ch);
			for (ClientHandler ch : threads) {
				if (ch.connected() && !ch.inGame()) {
					ch.sendMessage(LOBBY + lobby);
				}
			}
		}
	}

	/**
	 * Sends a message using the collection of connected ClientHandlers to all
	 * connected Clients with the chat feature.
	 * 
	 * @param msg
	 *            message that is send
	 */
	/*@ requires msg != null;
		requires msg.startsWith(CHAT);
	 */
	public void broadcastChat(String msg) {
		synchronized (threads) {
			mui.addMessage("Chat: " + msg);
			//@ loop_invariant threads.contains(ch);
			for (ClientHandler ch : threads) {
				if (ch.connected() && ch.hasChat()) {
					ch.sendMessage(msg);
				}
			}
		}
	}

	/**
	 * Print the message on the server view.
	 *
	 * @param msg
	 *            message that is printed
	 */
	//@ requires msg != null;
	public void print(String msg) {
		mui.addMessage(msg);
	}

	/**
	 * Checks if a client with the specified name exists.
	 *
	 * @param name
	 *            name of the client
	 * @return true, if the name is found
	 */
	/*@ pure */public boolean nameExists(String name) {
		synchronized (threads) {
			boolean exists = false;
			//@ loop_invariant threads.contains(ch);
			for (ClientHandler ch : threads) {
				if (name.equals(ch.getClientName())) {
					exists = true;
					break;
				}
			}
			return exists;
		}
	}

	/**
	 * Returns the client with the specified name.
	 *
	 * @param name
	 *            name of the client
	 * @return the client
	 */
	/*@ requires name != null;
		requires nameExists(name);
	 */
	/*@ pure */public ClientHandler getClient(String name) {
		synchronized (threads) {
			ClientHandler client = null;
			//@ loop_invariant threads.contains(ch);
			for (ClientHandler ch : threads) {
				if (ch.connected() && ch.getClientName().equals(name)) {
					client = ch;
					break;
				}
			}
			return client;
		}
	}

	/**
	 * Sends a message to the client with the specified name.
	 *
	 * @param name
	 *            name of the client
	 * @param msg
	 *            message that is send
	 */
	/*@ requires name != null;
		requires nameExists(name);
		requires msg != null;
	 */
	public void sendMessage(String name, String msg) {
		mui.addMessage("Message to " + name + ": " + msg);
		getClient(name).sendMessage(msg);
	}

	/**
	 * Checks wether the client with the specified name is in a game.
	 *
	 * @param name
	 *            name of the client
	 * @return true, if the client has a board
	 */
	/*@ requires name != null;
		requires nameExists(name);
	*/
	/*@ pure */public boolean inGame(String name) {
		return getClient(name).inGame();
	}

	/**
	 * Checks if the client with the specified name has the custom board size
	 * feature.
	 *
	 * @param name
	 *            the name
	 * @return true, if successful
	 */
	/*@ requires name != null;
		requires nameExists(name);
	*/
	/*@ pure */public boolean hasCustomBoardSize(String name) {
		return getClient(name).hasCustomBoardSize();
	}

	/**
	 * Looks up the specified invite, generates a board with the boardsize
	 * specified in the invite and assignes the board to both clients.
	 *
	 * @param name
	 *            the name of the client
	 * @param invited
	 *            the invited client
	 */
	/*@ requires name != null;
		requires nameExists(name);
		requires isInvited(name, invited);
	*/
	public void generateBoard(String name, String invited) {
		synchronized (invites) {
			Board board = null;
			String[] invite = getInvite(name, invited);
			Integer[] boardSize = invites.get(invite);
			invites.remove(invite);
			board = new Board(boardSize[1].intValue(), boardSize[0].intValue());
			board.addObserver(mui);
			mui.addMessage("Created a board for " + name + " and " + invited
					+ " with code " + board.hashCode());
			setBoard(name, board);
			setBoard(invited, board);
		}
	}

	/**
	 * Sets the board for the clientHandler with the specified name.
	 *
	 * @param name
	 *            name of the client
	 * @param board
	 *            board that is send
	 */
	/*@ requires name != null;
		requires nameExists(name);
		requires board != null;
		ensures getClient(name).getBoard() == board;
	*/
	private void setBoard(String name, Board board) {
		mui.addMessage("Set board for " + name + ".");
		getClient(name).setBoard(board);
	}

	/**
	 * Sends an string with the connected client names that aren't playing a
	 * game.
	 *
	 * @return the lobby
	 */
	/*@ pure */public String lobbyToString() {
		synchronized (threads) {
			String clients = "";
			//@ loop_invariant threads.contains(ch);
			for (ClientHandler ch : threads) {
				if (ch.connected() && !ch.inGame()) {
					clients += " " + ch.getClientName();
				}
			}
			return clients;
		}
	}

	/**
	 * Add a ClientHandler to the collection of ClientHandlers.
	 * 
	 * @param handler
	 *            ClientHandler that will be added
	 */
	/*@ requires handler != null;
		ensures getHandlers().contains(handler);
	 */
	public void addHandler(ClientHandler handler) {
		synchronized (threads) {
			threads.add(handler);
			mui.addMessage("Added clientHandler.");
		}
	}

	/**
	 * Gets the set of connected client Handlers.
	 * 
	 * @return threads, the set of connected clientHandlers
	 */
	/*@ pure */public HashSet<ClientHandler> getHandlers() {
		return threads;
	}

	/**
	 * Remove a ClientHandler from the collection of ClientHanlders.
	 * 
	 * @param handler
	 *            ClientHandler that will be removed
	 */
	/*@ requires handler != null;
		ensures !getHandlers().contains(handler);
	 */
	public void removeHandler(ClientHandler handler) {
		synchronized (threads) {
			threads.remove(handler);
			mui.addMessage("Removed clientHandler.");
		}
	}

	/**
	 * Add the names of the inviting and the invited client in a map with the
	 * specified boardsize.
	 *
	 * @param name
	 *            name of the inviting client
	 * @param invited
	 *            name of the invited client
	 * @param boardX
	 *            the amount of columns the board should have
	 * @param boardY
	 *            the amount of rowss the board should have
	 */
	/*@ requires name != null;
		requires nameExists(name);
		requires invited != null;
		requires nameExists(invited);
		requires boardX >= 4 & boardX <= 100;
		requires boardY >= 4 & boardY <= 100;
		ensures isInvited(name, invited);
	*/
	public void addInvite(String name, String invited, int boardX, int boardY) {
		synchronized (invites) {
			invites.put(new String[] { name, invited }, new Integer[] { boardX,
					boardY });
			mui.addMessage("Added invite from " + name + " to " + invited
					+ " with boardsize " + boardX + " x " + boardY + ".");
		}
	}

	/**
	 * Checks whether the client is invited.
	 *
	 * @param name
	 *            the name of the client
	 * @return true, if is invited
	 */
	/*@ requires name != null;
		requires nameExists(name);
	*/
	/*@ pure */public boolean isInvited(String name) {
		synchronized (invites) {
			boolean retBool = false;
			//@ loop_invariant invites.containsKey(invite);
			for (String[] invite : invites.keySet()) {
				if (invite[0].equals(name) || invite[1].equals(name)) {
					retBool = true;
					break;
				}
			}
			return retBool;
		}
	}

	/**
	 * Checks whether the client is invited by the client with the specified
	 * name.
	 *
	 * @param name
	 *            the name of the client that send the invite
	 * @param invited
	 *            the name of the client that received the invite
	 * @return true, if is invited
	 */
	/*@ requires name != null;
		requires nameExists(name);
		requires invited != null;
		requires nameExists(invited);
	*/
	/*@ pure */public boolean isInvited(String name, String invited) {
		synchronized (invites) {
			boolean retBool = false;
			//@ loop_invariant invites.containsKey(invite);
			for (String[] invite : invites.keySet()) {
				if (invite[0].equals(name) && invite[1].equals(invited)) {
					retBool = true;
					break;
				}
			}
			return retBool;
		}
	}

	/**
	 * Gets the map of invites.
	 * 
	 * @return the map of invites
	 */
	/*@ pure */public HashMap<String[], Integer[]> getInvites() {
		return invites;
	}

	/**
	 * Returns the invite with the specified names.
	 * 
	 * @param name
	 *            name of the client who send the invite
	 * @param invited
	 *            name of th client who received the invite
	 * @return the invite, a String[] with both names
	 */
	/*@ requires name != null;
		requires nameExists(name);
		requires invited != null;
		requires nameExists(invited);
		requires isInvited(name, invited);
		ensures getInvites().containsKey(\result);
	 */
	/*@ pure */public String[] getInvite(String name, String invited) {
		synchronized (invites) {
			String[] retInvite = null;
			//@ loop_invariant invites.containsKey(invite);
			for (String[] invite : invites.keySet()) {
				if (invite[0].equals(name) && invite[1].equals(invited)) {
					retInvite = invite;
					break;
				}
			}
			return retInvite;
		}
	}

	/**
	 * Removes all invites of the client with the specified name.
	 * 
	 * @param name
	 *            the name of the client
	 */
	/*@ requires name != null;
		requires nameExists(name);
		ensures !isInvited(name);
	*/
	public void removeInvite(String name) {
		synchronized (invites) {
			mui.addMessage("removing all invites with " + name + ".");
			//@ loop_invariant invites.containsKey(invite);
			for (String[] invite : invites.keySet()) {
				if (invite[0].equals(name)) {
					sendMessage(invite[1], Server.DECLINE_INVITE + " " + name);
					invites.remove(invite);
					mui.addMessage("Server removed invite from " + invite[0]
							+ " to " + invite[1] + ".");
				} else if (invite[1].equals(name)) {
					sendMessage(invite[0], Server.DECLINE_INVITE + " " + name);
					invites.remove(invite);
					mui.addMessage("Server removed invite from " + invite[0]
							+ " to " + invite[1] + ".");
				}
			}
		}
	}

	/**
	 * Removes the invite of the client with the specified name.
	 * 
	 * @param name
	 *            the name of the client
	 * @param invited
	 *            the name of the invited client
	 */
	/*@ requires name != null;
		requires nameExists(name);
		requires invited != null;
		requires nameExists(invited);
		ensures !isInvited(name, invited);
	*/
	public void removeInvite(String name, String invited) {
		synchronized (invites) {
			//@ loop_invariant invites.containsKey(invite);
			for (String[] invite : invites.keySet()) {
				if (invite[0].equals(name) && invite[1].equals(invited)) {
					invites.remove(invite);
					mui.addMessage("Server removed invite from " + name
							+ " to " + invited + ".");
					break;
				}
			}
		}
	}

	/**
	 * Generates a line with all players on the leaderboard.
	 * 
	 * @return a line with all players on the leaderboard.
	 */
	/*@ pure */public String leaderboardToString() {
		synchronized (leaderboard) {
			String scores = "";
			int rank = 0;
			LeaderboardPair oldPair = null;
			/*@ loop_invariant 0 <= i && i <= 50;
				loop_invariant i <= leaderboard.size();
				loop_invariant 0 <= rank && rank <= i;
			*/
			for (int i = 0; i < leaderboard.size(); i++) {
				if (i < 50) {
					LeaderboardPair pair = leaderboard.get(i);
					if (!pair.equalScore(oldPair)) {
						rank++;
						oldPair = pair;
					}
					scores += " " + pair + " " + rank;
				} else {
					break;
				}
			}
			return scores;
		}
	}

	/**
	 * Updates the score of the LeaderboardPair with the givin name. If the name
	 * doesn't exists it creates a new LeaderboardPair. If win is null 1 is
	 * added to games played and if it's true or false 1 is added to gamse
	 * playad and to games won or games lost repectively. Then sorts the
	 * leaderboardbased on the natural ordering of leaderboardpair.
	 * 
	 * @param name
	 *            Name of he LeaderboardPair
	 * @param win
	 *            Whether the player has won, lost or there was a draw.
	 */
	//@ requires name != null;
	public void updateLeaderboard(String name, Boolean win) {
		synchronized (leaderboard) {
			boolean found = false;
			//@ loop_invariant leaderboard.contains(pair);
			for (LeaderboardPair pair : leaderboard) {
				if (pair.getName().equals(name)) {
					if (win == null) {
						pair.updateDraw();
						mui.addMessage("Leaderboard: Added draw to " + name
								+ ".");
					} else if (win) {
						pair.updateWin();
						mui.addMessage("Leaderboard: Added win to " + name
								+ ".");
					} else {
						pair.updateLoss();
						mui.addMessage("Leaderboard: Added loss to " + name
								+ ".");
					}
					found = true;
					break;
				}
			}
			if (!found) {
				LeaderboardPair pair = null;
				if (win == null) {
					pair = new LeaderboardPair(name, 0, 0, 1);
					mui.addMessage("Leaderboard: Created new entry for " + name
							+ " with 1 draw.");
				} else if (win) {
					pair = new LeaderboardPair(name, 1, 0, 1);
					mui.addMessage("Leaderboard: Created new entry for " + name
							+ " with 1 win.");
				} else {
					pair = new LeaderboardPair(name, 0, 1, 1);
					mui.addMessage("Leaderboard: Created new entry for " + name
							+ " with 1 loss.");
				}
				leaderboard.add(pair);
			}
			Collections.sort(leaderboard);
			writeLeaderboard();
		}
	}

	/**
	 * Gets the leaderboard.
	 * 
	 * @return the leaderboard, a ArrayList of LeaderboardPairs
	 */
	/*@ pure */public ArrayList<LeaderboardPair> getLeaderboard() {
		return leaderboard;
	}

	/**
	 * Tries to read the leaderboard from the file specified in the FILENAME
	 * final and creates and sorts an ArrayList with the read values.
	 * 
	 * @return the created ArrayList
	 * @throws IOException
	 *             if the file can't be found
	 */
	/*@ pure */public ArrayList<LeaderboardPair> readLeaderboard()
			throws IOException {
		BufferedReader in = new BufferedReader(new FileReader(FILENAME));
		ArrayList<LeaderboardPair> leaderboard = new ArrayList<LeaderboardPair>();
		//@ loop_invariant in != null;
		while (in.ready()) {
			String[] pair = in.readLine().split("\\s+");
			try {
				leaderboard.add(new LeaderboardPair(pair[0], Integer
						.parseInt(pair[1]), Integer.parseInt(pair[2]), Integer
						.parseInt(pair[3])));
			} catch (NumberFormatException | ArrayIndexOutOfBoundsException e) {
				mui.addMessage("Error couldn't read leaderboard entry");
				/*
				 * Incorrect entry. Tries to continue to read entries, if all entries are
				 * incorrect none will be added and an empty set will be returned.
				 */
				continue;
			}
		}
		in.close();
		Collections.sort(leaderboard);
		return leaderboard;
	}

	/**
	 * Tries to write the leaderboard to the file specified in the FILENAME
	 * final. If the write fails an error will be printed, but the server won't
	 * terminate.
	 */
	public void writeLeaderboard() {
		PrintWriter out = null;
		try {
			out = new PrintWriter(FILENAME);
		} catch (FileNotFoundException e) {
			mui.addMessage("Error couldn't save leaderboard.");
			return;
		}
		/*@ loop_invariant out != null;
			loop_invariant leaderboard.contains(pair);
		*/
		for (LeaderboardPair pair : leaderboard) {
			out.println(pair);
		}
		// checkError() also flushes the stream.
		if (out.checkError()) {
			mui.addMessage("Error couldn't save leaderboard.");
		}
		out.close();
	}
}
