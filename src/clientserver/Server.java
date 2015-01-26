package clientserver;

import game.Board;

import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectInputStream;
import java.io.ObjectOutput;
import java.io.ObjectOutputStream;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.HashMap;
import java.util.HashSet;
import java.util.TreeSet;

// TODO: Auto-generated Javadoc
/**
 * Server. A Thread class that listens to a socket connection on a specified
 * port. For every socket connection with a Client, a new ClientHandler thread
 * is started.<br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */
public class Server extends Thread {
	// PROTOCOL
	/** The Constant ACCEPT_CONNECT. */
	public static final String ACCEPT_CONNECT = "OK";

	/** The Constant ERROR. */
	public static final String ERROR = "ERROR";

	/** The Constant LOBBY. */
	public static final String LOBBY = "LOBBY";

	/** The Constant INVITE. */
	public static final String INVITE = "INVITE";

	public static final String DECLINE_INVITE = "DECLINE";

	/** The Constant GAME_START. */
	public static final String GAME_START = "START";

	/** The Constant GAME_END. */
	public static final String GAME_END = "END";

	/** The Constant REQUEST_MOVE. */
	public static final String REQUEST_MOVE = "REQUEST";

	/** The Constant MOVE_OK. */
	public static final String MOVE_OK = "MOVE";

	/** The Constant BOARD. */
	public static final String BOARD = "BOARD";

	/** The Constant CHAT. */
	public static final String CHAT = "CHAT";

	/** The Constant LEADERBOARD. */
	public static final String LEADERBOARD = "LEADERBOARD";

	public static final String PONG = "PONG";
	// END OF PROTOCOL

	public static final String FEATURES = Features.CHAT + " "
			+ Features.LEADERBOARD + " " + Features.CUSTOM_BOARD_SIZE;

	/** The Constant LEADERBOARD. */
	public static final String FILENAME = "leaderboard.obj";

	/**
	 * The port of the server.
	 */
	private ServerSocket ss;

	/**
	 * The User Interface of the server.
	 */
	private MessageUI mui;

	/** The threads. */
	private HashSet<ClientHandler> threads;

	/** The invites. */
	private HashMap<String[], Integer[]> invites;

	/** The leaderboard. */
	private TreeSet<LeaderboardPair> leaderboard;

	/**
	 * Constructs a new Server object.
	 *
	 * @param portArg
	 *            the port of the server
	 * @param muiArg
	 *            the view of the server
	 * @throws IOException
	 */
	/*@ requires portArg >= 1 & portArg <= 65535;
		requires muiArg != null;
	 */
	@SuppressWarnings("unchecked")
	public Server(int portArg, MessageUI muiArg) throws IOException {
		this.ss = new ServerSocket(portArg);
		this.mui = muiArg;
		this.threads = new HashSet<ClientHandler>();
		this.invites = new HashMap<String[], Integer[]>();
		try {
			ObjectInput in = new ObjectInputStream(
					new FileInputStream(FILENAME));
			/*
			 * It is not possible to use instanceof on a TreeSet<CustomClass>,
			 * so the cast will always be unchecked. But we assume the file is
			 * created and written by this server, so it is a instance of
			 * TreeSet<LeaderboardPair>. But even if it isn't (maybe written by
			 * another program) we also catch a ClassCastException and create a
			 * new leaderboard, so it should be fine, that's why the unchecked
			 * warning is supressed
			 */
			this.leaderboard = (TreeSet<LeaderboardPair>) in.readObject();
			in.close();
		} catch (IOException | ClassNotFoundException | ClassCastException e) {
			this.leaderboard = new TreeSet<LeaderboardPair>();
		}
	}

	/**
	 * Listens to a port of this Server if there are any Clients that would like
	 * to connect. For every new socket connection a new ClientHandler thread is
	 * started that takes care of the further communication with the Client.
	 */
	public void run() {
		while (true) {
			try {
				Socket s = ss.accept();
				ClientHandler ch = new ClientHandler(this, s);
				addHandler(ch);
				ch.start();
			} catch (IOException e) {
				mui.addMessage("Error adding client");
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
			for (ClientHandler ch : threads) {
				if (ch.connected()) {
					ch.sendMessage(msg);
				}
			}
			mui.addMessage("Broadcast: " + msg);
		}
	}

	/**
	 * Sends a message using the collection of connected ClientHandlers to all
	 * connected Clients without a game.
	 */
	public void broadcastLobby() {
		synchronized (threads) {
			for (ClientHandler ch : threads) {
				if (!ch.inGame()) {
					ch.sendMessage(LOBBY + getLobby());
				}
			}
			mui.addMessage("Lobby:" + getLobby());
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
			for (ClientHandler ch : threads) {
				if (ch.connected() && ch.hasChat()) {
					ch.sendMessage(msg);
				}
			}
			mui.addMessage("Chat: " + msg);
		}
	}

	/**
	 * Print the message on the server ui.
	 *
	 * @param msg
	 *            message that is printed
	 */

	//@ requires msg != null;
	public void print(String msg) {
		mui.addMessage(msg);
	}

	/**
	 * Checks if the name exists.
	 *
	 * @param name
	 *            the name
	 * @return true, if the name is found
	 */
	/*@ pure */public boolean nameExists(String name) {
		synchronized (threads) {
			boolean exists = false;
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
	 *            the name
	 * @return the client
	 */
	/*@ requires name != null;
		requires nameExists(name);
	 */
	/*@ pure */public ClientHandler getClient(String name) {
		synchronized (threads) {
			ClientHandler client = null;
			for (ClientHandler ch : threads) {
				if (ch.getClientName().equals(name)) {
					client = ch;
					break;
				}
			}
			return client;
		}
	}

	/**
	 * Sends a message to the Client with the specified name.
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
		getClient(name).sendMessage(msg);
		mui.addMessage("Server send message to " + name + ": " + msg);
	}

	/**
	 * Checks wether the client with the specified name is in a game.
	 *
	 * @param name
	 *            name of the client
	 * @return true, if successful
	 */
	/*@ requires name != null;
		requires nameExists(name);
	*/
	/*@ pure */public boolean inGame(String name) {
		return getClient(name).inGame();
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
	*/
	private void setBoard(String name, Board board) {
		// TODO: Game maken inplaats van bord?
		getClient(name).setBoard(board);
		mui.addMessage("Server set board for " + name);
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
	 * Sends an string with the connected client names that aren't playing a
	 * game.
	 *
	 * @return the lobby
	 */
	/*@ pure */public String getLobby() {
		synchronized (threads) {
			String clients = "";
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
	 */
	// TODO: maak getters voor alle lijsten om te ensuren
	public void addHandler(ClientHandler handler) {
		synchronized (threads) {
			threads.add(handler);
		}
	}

	/**
	 * Remove a ClientHandler from the collection of ClientHanlders.
	 * 
	 * @param handler
	 *            ClientHandler that will be removed
	 */
	//@ requires handler != null;
	public void removeHandler(ClientHandler handler) {
		synchronized (threads) {
			threads.remove(handler);
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
	 *            the board x
	 * @param boardY
	 *            the board y
	 */
	/*@ requires name != null;
		requires nameExists(name);
		requires invited != null;
		requires nameExists(invited);
		requires boardX > 0;
		requires boardY > 0;
	*/
	public void addInvite(String name, String invited, int boardX, int boardY) {
		synchronized (invites) {
			invites.put(new String[] { name, invited }, new Integer[] { boardX,
					boardY });
		}
	}

	public String[] getInvite(String name, String invited) {
		synchronized (invites) {
			String[] retInvite = null;
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
		requires nameExists(invited);;
	*/
	/*@ pure */public boolean isInvited(String name, String invited) {
		synchronized (invites) {
			boolean retBool = false;
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
	 * Removes all invites of the client with the specified name.
	 * 
	 * @param name
	 *            the name of the client
	 */
	/*@ requires name != null;
		requires nameExists(name);
	*/
	public void removeInvite(String name) {
		synchronized (invites) {
			for (String[] invite : invites.keySet()) {
				if (invite[0].equals(name)) {
					sendMessage(invite[1], Server.DECLINE_INVITE + " " + name);
					invites.remove(invite);
				} else if (invite[1].equals(name)) {
					sendMessage(invite[0], Server.DECLINE_INVITE + " " + name);
					invites.remove(invite);
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
		requires nameExists(invited);;
	*/
	public void removeInvite(String name, String invited) {
		synchronized (invites) {
			for (String[] invite : invites.keySet()) {
				if (invite[0].equals(name) && invite[1].equals(invited)) {
					invites.remove(invite);
					break;
				}
			}
		}
	}

	/**
	 * Generates a line with all players on the leaderboard.
	 */
	public String getLeaderboard() {
		synchronized (leaderboard) {
			String scores = "";
			int rank = 0;
			LeaderboardPair oldPair = null;
			for (LeaderboardPair pair : leaderboard) {
				if (!pair.equalScore(oldPair)) {
					rank++;
					oldPair = pair;
				}
				scores += " " + pair.getName() + " " + pair.getWins() + " "
						+ pair.getLosses() + " " + pair.getGames() + " " + rank;
			}
			return scores;
		}
	}

	/**
	 * Updates the score of the LeaderboardPair with the givin name. If the name
	 * doesn't exists it creates a new LeaderboardPair. If win is null 1 is
	 * added to games played and if it's true or false 1 is added to gamse
	 * playad and to games won or games lost repectively.
	 * 
	 * @param name
	 *            Name of he LeaderboardPair
	 * @param increment
	 *            Wether to increment or decrement the score
	 */
	/*@ requires name != null;
	 */
	public void updateLeaderboard(String name, Boolean win) {
		synchronized (leaderboard) {
			boolean found = false;
			for (LeaderboardPair pair : leaderboard) {
				if (pair.getName().equals(name)) {
					if (win == null) {
						pair.updateDraw();
					} else if (win) {
						pair.updateWin();
					} else {
						pair.updateLoss();
					}
					found = true;
					break;
				}
			}
			if (!found) {
				LeaderboardPair pair = new LeaderboardPair(name);
				if (win == null) {
					pair.updateDraw();
				} else if (win) {
					pair.updateWin();
				} else {
					pair.updateLoss();
				}
				leaderboard.add(pair);
			}
			try {
				ObjectOutput out = new ObjectOutputStream(new FileOutputStream(
						FILENAME));
				out.writeObject(leaderboard);
				out.flush();
				out.close();
			} catch (IOException e) {
				mui.addMessage("Error couldn't save leaderboard");
			}
		}
	}
}
